from langchain.embeddings import HuggingFaceEmbeddings
from langchain.vectorstores import FAISS
from langchain.text_splitter import RecursiveCharacterTextSplitter
import re
from dataclasses import dataclass
from typing import Optional, List, Tuple
import logging

import yaml

with open("Src/Config.yml") as file:
    config = yaml.safe_load(file)

@dataclass
class ContentChunk:
    content: str
    chunk_type: str
    context: Optional[str] = None

class VerilogTextbookProcessor:
    def __init__(self):
        self.code_embeddings = HuggingFaceEmbeddings(model_name="microsoft/codebert-base")
        self.text_embeddings = HuggingFaceEmbeddings(model_name="sentence-transformers/all-mpnet-base-v2")
        self.code_vectorstore = FAISS.from_texts([], self.code_embeddings)
        self.text_vectorstore = FAISS.from_texts([], self.text_embeddings)
        self.logger = logging.getLogger(__name__)
        # Separate patterns for code and queries
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
        """Detect Verilog code"""
        return any(re.search(pattern, text, re.MULTILINE)
                  for pattern in self.code_patterns)
    def is_code_query(self, text: str) -> bool:
        """Specifically detect code-related queries"""
        return (
            any(re.search(pattern, text, re.MULTILINE | re.IGNORECASE)
                for pattern in self.query_patterns) or
            self.is_verilog(text)
        )
    def get_context_window(self, text: str, start: int, end: int, window_size: int = 200) -> str:
        """Get surrounding context with proper paragraph boundaries"""
        context_start = max(0, start - window_size)
        context_end = min(len(text), end + window_size)
        # Expand to paragraph boundaries
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
        """Extract Verilog code blocks with improved context handling"""
        code_pattern = r'(?:verilog)?\s*(.*?)'
        positions = []
        for match in re.finditer(code_pattern, text, re.DOTALL):
            start, end = match.span()
            code = match.group(1).strip()
            if self.is_verilog(code):
                context = self.get_context_window(text, start, end)
                positions.append((start, end, code, context))
        return positions
    def process_chunk(self, chunk: ContentChunk):
        """Process chunks with metadata preservation"""
        try:
            metadata = {
                "type": chunk.chunk_type,
                "context": chunk.context
            }
            if chunk.chunk_type == "code":
                # For code, include context in the indexed content
                content = f"{chunk.context}\n\n{chunk.content}" if chunk.context else chunk.content
                self.code_vectorstore.add_texts([content], metadatas=[metadata])
            else:
                self.text_vectorstore.add_texts([chunk.content], metadatas=[metadata])
        except Exception as e:
            self.logger.error(f"Error processing chunk: {str(e)}")

    def split_content(self, text: str) -> List[ContentChunk]:
        chunks = []
        last_end = 0
        try:
            positions = self.extract_code_blocks(text)
            for start, end, code, context in positions:
                # Add text before code block
                if start > last_end:
                    chunks.append(ContentChunk(
                        content=text[last_end:start].strip(),
                        chunk_type="text"
                    ))
                # Add code block with context
                chunks.append(ContentChunk(
                    content=code,
                    chunk_type="code",
                    context=context
                ))
                last_end = end
            # Add remaining text
            if last_end < len(text):
                chunks.append(ContentChunk(
                    content=text[last_end:].strip(),
                    chunk_type="text"
                ))
        except Exception as e:
            self.logger.error(f"Error splitting content: {str(e)}")
            # Return whole text as single chunk if parsing fails
            chunks = [ContentChunk(content=text, chunk_type="text")]
        return chunks

    def process_document(self, content: str):
        chunks = self.split_content(content)
        for chunk in chunks:
            self.process_chunk(chunk)

    def query(self, question: str, k: int = 3) -> List[ContentChunk]:
        """Improved query routing with better classification"""
        is_code_query = self.is_code_query(question)
        try:
            if is_code_query and self.code_vectorstore.index:
                results = self.code_vectorstore.similarity_search(question, k=k)
            elif not is_code_query and self.text_vectorstore.index:
                results = self.text_vectorstore.similarity_search(question, k=k)
            else:
                # Fallback to the other store if primary is empty
                results = (self.text_vectorstore if self.text_vectorstore.index else self.code_vectorstore).similarity_search(question, k=k)
            return [ContentChunk(
                content=doc.page_content,
                chunk_type=doc.metadata.get('type', 'unknown'),
                context=doc.metadata.get('context')
            ) for doc in results]
        except Exception as e:
            self.logger.error(f"Error during query: {str(e)}")
            return []


import PyPDF2
import sys
import re
#from verilog_processor import VerilogTextbookProcessor

def clean_pdf_text(text):
    text = text.replace('\f', '\n\n')
    text = re.sub(r'(?<=[a-z])-\n(?=[a-z])', '', text)
    text = re.sub(r'\s+', ' ', text)
    text = re.sub(r'\s*\n', '', text)
    return text

def pdf_to_text(pdf_path):
    with open(pdf_path, 'rb') as file:
        pdf_reader = PyPDF2.PdfReader(file)
        text = ""
        for page in pdf_reader.pages:
            text += page.extract_text() + "\n\n"
    return clean_pdf_text(text)

if __name__ == "__main__":

    PDF_Name = config["PDF_Name"]
    pdf_text = pdf_to_text(f"VerilogTextBooks/{PDF_Name}.pdf")
    processor = VerilogTextbookProcessor()
    processor.process_document(pdf_text)
    results = processor.query("How to implement a D flip-flop?")
    for chunk in results:
        print(f"Type: {chunk.chunk_type}")
        print(f"Content: {chunk.content}")
        print("---")

