from langchain_community.document_loaders import PyMuPDFLoader
import pandas as pd
import csv
import os
import yaml

# Load your PDFs
PDF_Name = "CernyDudani-SVA- The Power of Assertions in SystemVerilog"
Folder_Name = f"Book1-{PDF_Name}"
pdf_loader = PyMuPDFLoader(f"VerilogTextBooks/{PDF_Name}.pdf")
documents = pdf_loader.load()

# If you have multiple PDFs, you can load them in a loop
# pdf_paths = ["path/to/doc1.pdf", "path/to/doc2.pdf"]
# documents = []
# for path in pdf_paths:
#     loader = PyMuPDFLoader(path)
#     documents.extend(loader.load())

from langchain.text_splitter import RecursiveCharacterTextSplitter

# Split the PDF text into chunks
text_splitter = RecursiveCharacterTextSplitter(chunk_size=300, chunk_overlap=50)
chunks = text_splitter.split_documents(documents)

from langchain_openai import OpenAIEmbeddings
# from langchain_community.embeddings import OpenAIEmbeddings
from langchain_community.vectorstores import FAISS

# Initialize embeddings
with open("Src/Config.yml") as file:
    config = yaml.safe_load(file)

OpenAI_API_Key = config["Openai_API_Key"]
embeddings = OpenAIEmbeddings(openai_api_key=OpenAI_API_Key)

# Index the document chunks in a vector store
vector_store = FAISS.from_texts([chunk.page_content for chunk in chunks], embeddings)
if not os.path.exists(f"RAG_Database/{Folder_Name}"):
    os.makedirs(f"RAG_Database/{Folder_Name}")
vector_store.save_local(f"RAG_Database/{Folder_Name}")

# test vector_store
# loaded_vector_store = FAISS.load_local(f"RAG_Database/{Folder_Name}",embeddings,allow_dangerous_deserialization=True)
# query = "Please explain different types of verilog assertions."
# retriever = loaded_vector_store.as_retriever()
# results = retriever.get_relevant_documents(query)
# for doc in results:
#     print(doc.page_content)