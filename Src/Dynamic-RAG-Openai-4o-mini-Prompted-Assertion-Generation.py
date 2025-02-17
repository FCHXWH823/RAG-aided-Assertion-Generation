# Author Derek Ekberg
import re
from dataclasses import dataclass
from typing import Optional, List, Tuple, Dict, Any
import logging
import numpy as np
from sentence_transformers import SentenceTransformer
import torch
from transformers import AutoTokenizer, AutoModel
import yaml
from PyMuPDF import *
@dataclass
class ContentChunk:
    content: str
    chunk_type: str
    context: Optional[str] = None
    context_upper: Optional[str] = None
    context_lower: Optional[str] = None

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
        self.code_patterns = [
            r'\b(module|endmodule)\b',
            r'always\s*@',
            r'\b(input|output|inout)\b',
            r'assign\s+\w+',
            r'reg|wire'
        ]
        self.query_patterns = [
            r'\b(show|implement|code|write|syntax)\b',
            r'\bverilog\b',
            r'\b(module|circuit)\b'
        ]
    def is_verilog(self, text: str) -> bool:
        return any(re.search(pattern, text, re.MULTILINE)
                   for pattern in self.code_patterns)
    def is_code_query(self, text: str) -> bool:
        return (
                any(re.search(pattern, text, re.MULTILINE | re.IGNORECASE)
                    for pattern in self.query_patterns) or
                self.is_verilog(text)
        )
    def get_context_window(self, text: str, start: int, end: int, window_size: int = 200) -> str:
        context_start = max(0, start - window_size)
        context_end = min(len(text), end + window_size)
        if context_start > 0:
            para_start = text.rfind('\n\n', context_start, start)
            if para_start != -1:
                context_start = para_start + 2
        if context_end < len(text):
            para_end = text.find('\n\n', end, context_end)
            if para_end != -1:
                context_end = para_end
        return text[context_start:context_end].strip()
    def extract_code_blocks(self, text: str) -> List[Tuple[int, int, str, str]]:
        code_pattern = r'(?:verilog)?\s*(.*?)'
        positions = []
        for match in re.finditer(code_pattern, text, re.DOTALL):
            start, end = match.span()
            code = match.group(1).strip()
            if self.is_verilog(code):
                context = self.get_context_window(text, start, end)
                positions.append((start, end, code, context))
        return positions
    # def process_chunk(self, chunk: ContentChunk):
    #     try:
    #         metadata = {"type": chunk.chunk_type, "context": chunk.context}
    #         if chunk.chunk_type == "code":
    #             content = f"{chunk.context}\n\n{chunk.content}" if chunk.context else chunk.content
    #             self.code_vectorstore.add_texts([content], [metadata])
    #         else:
    #             self.text_vectorstore.add_texts([chunk.content], [metadata])
    #     except Exception as e:
    #         self.logger.error(f"Error processing chunk: {str(e)}")
    
    def process_chunk(self, chunk: ContentChunk):
        metadata = {"type": chunk.chunk_type, "context_upper": chunk.context_upper, "context_lower": chunk.context_lower}
        if chunk.chunk_type == "code":
            content = f"{chunk.context_upper}\n\n{chunk.content}\n\n{chunk.context_lower}"
            self.code_vectorstore.add_texts([content], [metadata])
        else:
            self.text_vectorstore.add_texts([chunk.content], [metadata])

    def process_document(self, blocks):
        for i in range(len(blocks)):
            block = blocks[i]
            if block["type"] == "text":
                self.process_chunk(ContentChunk(
                    content=block_to_text(block).strip(),
                    chunk_type="text"
                ))
            if block["type"] == "code":
                self.process_chunk(ContentChunk(
                    content=block_to_text(block),
                    chunk_type="code",
                    context_upper=block_to_text(blocks[i-1]) if i==0 else "",
                    context_lower=block_to_text(blocks[i+1]) if i==len(blocks)-1 else ""
                ))
            print(f"{i}-th block finished")

    # def process_document(self, content: str):
    #     try:
    #         positions = self.extract_code_blocks(content)
    #         last_end = 0
    #         for start, end, code, context in positions:
    #             if start > last_end:
    #                 self.process_chunk(ContentChunk(
    #                     content=content[last_end:start].strip(),
    #                     chunk_type="text"
    #                 ))
    #             self.process_chunk(ContentChunk(
    #                 content=code,
    #                 chunk_type="code",
    #                 context=context
    #             ))
    #             last_end = end
    #         if last_end < len(content):
    #             self.process_chunk(ContentChunk(
    #                 content=content[last_end:].strip(),
    #                 chunk_type="text"
    #             ))
    #     except Exception as e:
    #         self.logger.error(f"Error processing document: {str(e)}")

    def query(self, question: str, k: int = 3) -> List[ContentChunk]:
        is_code_query = self.is_code_query(question)
        print(f"is_code_query: {is_code_query}")
        
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


import PyPDF2
import re
from typing import Optional, List
import logging

def clean_text(text: str) -> str:
    """
    Clean and normalize text extracted from PDF.
    Handles common PDF extraction issues like split words and page breaks.
    """
    # Replace form feeds with paragraph breaks
    text = text.replace('\f', '\n\n')
    # Fix hyphenated words at line breaks (e.g. "pro-\ngram" -> "program")
    text = re.sub(r'(?<=[a-z])-\n(?=[a-z])', '', text)
    # Normalize whitespace while preserving paragraph breaks
    text = re.sub(r'[ \t]+', ' ', text)
    text = re.sub(r'\n\s*\n', '\n\n', text)
    text = re.sub(r'\n([^\n])', r' \1', text)
    return text.strip()
def pdf_to_text(pdf_path: str) -> Optional[str]:
    """
    Convert PDF to cleaned text that can be processed by VerilogTextbookProcessor.
    Args:
        pdf_path: Path to the PDF file
    Returns:
        Cleaned text content if successful, None if failed
    """
    try:
        with open(pdf_path, 'rb') as file:
            pdf_reader = PyPDF2.PdfReader(file)
            text_parts = []
            for page in pdf_reader.pages:
                text = page.extract_text()
                if text:
                    text_parts.append(text)
            full_text = '\n\n'.join(text_parts)
            return clean_text(full_text)
    except Exception as e:
        logging.error(f"Error processing PDF {pdf_path}: {str(e)}")
        return None
def main():
    with open("Src/Config.yml") as file:
        config = yaml.safe_load(file)
    
    PDF_Name = config["PDF_Name"]

    """Process PDF and optionally query the processed content."""
    # pdf_text = pdf_to_text(f"VerilogTextBooks/{PDF_Name}.pdf")
    processor = VerilogTextbookProcessor()
    # print(len(pdf_text))
    blocks = get_pdf_blocks(f"VerilogTextBooks/{PDF_Name}.pdf")
    # processor.process_document(pdf_text)
    processor.process_document(blocks)
    results = processor.query("How to implement a D flip-flop?")
    print(len(results))
    for chunk in results:
        print(f"Type: {chunk.chunk_type}")
        print(f"Content: {chunk.content}")
        print("---")

if __name__ == "__main__":
    main()
