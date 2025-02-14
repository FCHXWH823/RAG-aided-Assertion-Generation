# Author Derek Ekberg

import re
from dataclasses import dataclass
from typing import Optional, List, Tuple, Dict, Any
import logging
import numpy as np
from sentence_transformers import SentenceTransformer
import torch
from transformers import AutoTokenizer, AutoModel

from verilog_patterns import VERILOG_PATTERNS, is_likely_prose


@dataclass
class ContentChunk:
    content: str
    chunk_type: str
    context: Optional[str] = None


class TransformerEmbeddings:
    def __init__(self, model_name: str):
        self.device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
        self.tokenizer = AutoTokenizer.from_pretrained(model_name)
        self.model = AutoModel.from_pretrained(model_name).to(self.device)

    def mean_pooling(self, model_output, attention_mask):
        token_embeddings = model_output[0]
        input_mask_expanded = attention_mask.unsqueeze(-1).expand(token_embeddings.size()).float()
        return torch.sum(token_embeddings * input_mask_expanded, 1) / torch.clamp(input_mask_expanded.sum(1), min=1e-9)

    def embed_texts(self, texts: List[str]) -> np.ndarray:
        encoded_input = self.tokenizer(texts, padding=True, truncation=True, max_length=512, return_tensors='pt')
        encoded_input = {k: v.to(self.device) for k, v in encoded_input.items()}

        with torch.no_grad():
            model_output = self.model(**encoded_input)

        embeddings = self.mean_pooling(model_output, encoded_input['attention_mask'])
        return embeddings.cpu().numpy()


class VectorStore:
    def __init__(self, embeddings_model: TransformerEmbeddings):
        self.embeddings = embeddings_model
        self.vectors = []
        self.texts = []
        self.metadatas = []

    def add_texts(self, texts: List[str], metadatas: Optional[List[Dict[str, Any]]] = None):
        if not texts:
            return
        if metadatas is None:
            metadatas = [{} for _ in texts]

        embeddings = self.embeddings.embed_texts(texts)
        self.vectors.extend(embeddings)
        self.texts.extend(texts)
        self.metadatas.extend(metadatas)

    def similarity_search(self, query: str, k: int = 3):
        if not self.texts:
            return []

        query_embedding = self.embeddings.embed_texts([query])[0]
        similarities = np.dot(self.vectors, query_embedding)
        top_k = np.argsort(similarities)[-k:][::-1]

        return [type('Document', (), {
            'page_content': self.texts[i],
            'metadata': self.metadatas[i]
        })() for i in top_k]


class VerilogTextbookProcessor:
    def __init__(self):
        self.code_embeddings = TransformerEmbeddings("microsoft/codebert-base")
        self.text_embeddings = TransformerEmbeddings("sentence-transformers/all-mpnet-base-v2")

        self.code_vectorstore = VectorStore(self.code_embeddings)
        self.text_vectorstore = VectorStore(self.text_embeddings)

        self.logger = logging.getLogger(__name__)
        logging.basicConfig(level=logging.INFO)

        self.code_patterns = VERILOG_PATTERNS

        self.query_patterns = [
            r'\b(show|implement|code|write|syntax)\b',
            r'\b(verilog|systemverilog|sva)\b',
            r'\b(module|circuit|interface|package|program)\b'
        ]

        self.inline_context_window = 100

    def is_verilog(self, text: str) -> bool:
        """Enhanced Verilog detection that accounts for inline code."""
        # Look for specific Verilog assertion patterns first
        assertion_patterns = [
            r'assert\s+property\s*\(',
            r'\$stable\s*\(',
            r'\|->\s*',
            r'@\s*\(\s*posedge\s+\w+\s*\)',
            r'\$error\s*\('
        ]

        # Check for assertion patterns first
        assertion_matches = sum(1 for pattern in assertion_patterns
                                if re.search(pattern, text, re.MULTILINE))
        if assertion_matches >= 2:  # If multiple assertion patterns found
            return True

        # Then check regular Verilog patterns
        if any(re.search(pattern, text, re.MULTILINE) for pattern in self.code_patterns):
            if not is_likely_prose(text):
                return True
            code_matches = sum(1 for pattern in self.code_patterns if re.search(pattern, text))
            return code_matches >= 2
        return False

    def is_code_query(self, text: str) -> bool:
        """Determine if query is asking for code."""
        return (
                any(re.search(pattern, text, re.MULTILINE | re.IGNORECASE)
                    for pattern in self.query_patterns) or
                self.is_verilog(text)
        )

    def get_context_window(self, text: str, start: int, end: int, window_size: int = 200) -> str:
        """Get context window around a code segment, handling inline code better."""
        context_start = max(0, start - window_size)
        context_end = min(len(text), end + window_size)

        # Try to expand to complete sentences
        while context_start > 0 and text[context_start - 1] not in '.!?\n':
            context_start -= 1
        while context_end < len(text) and text[context_end] not in '.!?\n':
            context_end += 1

        context = text[context_start:context_end].strip()

        # If context contains code markers, expand to include complete code blocks
        if '```' in context:
            pre_context = text[max(0, context_start - 100):context_start]
            post_context = text[context_end:min(len(text), context_end + 100)]

            # Find complete code block boundaries
            if '```' in pre_context:
                last_start = pre_context.rindex('```')
                context_start = context_start - (len(pre_context) - last_start)
            if '```' in post_context:
                first_end = post_context.index('```')
                context_end = context_end + first_end + 3

            context = text[context_start:context_end].strip()

        return context

    def extract_code_segments(self, text: str) -> List[Tuple[str, str]]:
        """Extract code segments and their context from text."""
        segments = []

        # First look for explicit code blocks
        code_blocks = re.finditer(r'```verilog(.*?)```', text, re.DOTALL)
        for match in code_blocks:
            code = match.group(1).strip()
            context = self.get_context_window(text, match.start(), match.end())
            segments.append((code, context))

        # Then look for inline assertions and code
        if not segments:  # Only look for inline if no explicit blocks found
            lines = text.split('\n')
            for line in lines:
                if self.is_verilog(line):
                    # Extract the actual code part from the line
                    code_match = re.search(r'(assert\s+property.*?;|initial\s+begin.*?end|always\s*@.*?;)',
                                           line, re.DOTALL)
                    if code_match:
                        code = code_match.group(1).strip()
                        segments.append((code, line.strip()))

        return segments

    def process_chunk(self, chunk: ContentChunk):
        """Process content chunk with enhanced text and code handling."""
        try:
            metadata = {"type": chunk.chunk_type, "context": chunk.context}

            if chunk.chunk_type == "code":
                # For code chunks, include context in the indexed content
                content = f"{chunk.context}\n\n{chunk.content}" if chunk.context else chunk.content
                self.code_vectorstore.add_texts([content], [metadata])
            else:
                # Extract any code segments first
                code_segments = self.extract_code_segments(chunk.content)

                # Add the full text content (without code blocks) to text vectorstore
                cleaned_text = re.sub(r'```verilog.*?```', '', chunk.content, flags=re.DOTALL)
                if cleaned_text.strip():
                    self.text_vectorstore.add_texts(
                        [cleaned_text.strip()],
                        [{"type": "text", "context": chunk.context}]
                    )

                # Add each code segment to code vectorstore
                for code, context in code_segments:
                    self.code_vectorstore.add_texts(
                        [code],
                        [{"type": "code", "context": context}]
                    )

        except Exception as e:
            self.logger.error(f"Error processing chunk: {str(e)}")

    def process_document(self, content: str):
        """Process document with enhanced code extraction."""
        try:
            # First pass: look for explicit code blocks
            code_blocks = re.finditer(r'```verilog(.*?)```', content, re.DOTALL)
            last_end = 0
            has_code_blocks = False

            for match in code_blocks:
                has_code_blocks = True
                start, end = match.span()

                # Process text before code block
                if start > last_end:
                    text_chunk = content[last_end:start].strip()
                    if text_chunk:
                        self.process_chunk(ContentChunk(
                            content=text_chunk,
                            chunk_type="text"
                        ))

                # Process code block
                code = match.group(1).strip()
                context = self.get_context_window(content, start, end)
                self.process_chunk(ContentChunk(
                    content=code,
                    chunk_type="code",
                    context=context
                ))
                last_end = end

            # Process remaining text or entire content if no code blocks found
            remaining_text = content[last_end:] if has_code_blocks else content
            if remaining_text.strip():
                self.process_chunk(ContentChunk(
                    content=remaining_text.strip(),
                    chunk_type="text"
                ))

        except Exception as e:
            self.logger.error(f"Error processing document: {str(e)}")

    def query(self, question: str, k: int = 3) -> List[ContentChunk]:
        """Query for content based on question."""
        is_code_query = self.is_code_query(question)

        try:
            results = (self.code_vectorstore if is_code_query else self.text_vectorstore).similarity_search(question,
                                                                                                            k=k)

            return [ContentChunk(
                content=doc.page_content,
                chunk_type=doc.metadata.get('type', 'unknown'),
                context=doc.metadata.get('context')
            ) for doc in results]

        except Exception as e:
            self.logger.error(f"Error during query: {str(e)}")
            return []


# Example usage
# if __name__ == "__main__":
#     test_content = """
#     4.2 Design Verification with Assertions

#     When verifying complex digital designs, it's crucial to implement robust assertion checks to catch potential timing violations and protocol errors. One of the most important aspects to verify is signal stability during active transfers. For this, we can use the assertion assert property (@(posedge clk) req ##1 $stable(req) |-> !abort) else $error("Request changed during active transfer!"); which ensures the request signal doesn't change unless an abort occurs. This common verification pattern helps catch timing violations early in the design process.

#     This type of assertion is particularly valuable in bus interfaces and handshaking protocols where signal stability is critical for proper operation. By monitoring the request signal's stability and allowing changes only when an abort is signaled, we can prevent glitches and ensure reliable data transfers. This verification approach can be extended to other control signals in your design as needed."""

#     print("\nProcessing test content with inline Verilog assertion...")

#     # Test the processor
#     processor = VerilogTextbookProcessor()
#     processor.process_document(test_content)

#     # Test queries
#     test_queries = [
#         "Show me assertions for request stability",
#         "What verification is needed for the request signal?",
#         "How do you verify request signals?",
#         "Show me Verilog code for request assertions"
#     ]

#     print("\nTesting queries for code and context retrieval:")
#     for query in test_queries:
#         print(f"\nQuery: {query}")
#         results = processor.query(query)
#         for i, result in enumerate(results, 1):
#             print(f"\nResult {i}:")
#             print(f"Type: {result.chunk_type}")
#             print(f"Content: {result.content}")
#             if result.context:
#                 print(f"Context: {result.context}")

