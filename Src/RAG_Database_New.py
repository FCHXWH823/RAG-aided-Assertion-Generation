from langchain_chroma import Chroma
from langchain_openai import OpenAIEmbeddings
from langchain.text_splitter import RecursiveCharacterTextSplitter
from langchain_community.document_loaders import PyMuPDFLoader
import pandas as pd
import csv
import os
import yaml
import getpass

with open("Src/Config.yml") as file:
    config = yaml.safe_load(file)
# Load your PDFs
# PDF_Name = "CernyDudani-SVA- The Power of Assertions in SystemVerilog"
PDF_Name = config["PDF_Name"]
OpenAI_API_Key = config["Openai_API_Key"]
Folder_Name = f"Book1-{PDF_Name}"

def collect_RAG_database():
    pdf_loader = PyMuPDFLoader(f"VerilogTextBooks/{PDF_Name}.pdf")
    documents = pdf_loader.load()
    print(len(documents))
    print(documents[0].page_content[0:100])
    print(documents[0].metadata)
    # If you have multiple PDFs, you can load them in a loop
    # pdf_paths = ["path/to/doc1.pdf", "path/to/doc2.pdf"]
    # documents = []
    # for path in pdf_paths:
    #     loader = PyMuPDFLoader(path)
    #     documents.extend(loader.load())

    
    text_splitter = RecursiveCharacterTextSplitter(chunk_size=1000, chunk_overlap=200)
    chunks = text_splitter.split_documents(documents)
    vector_store = Chroma.from_documents(documents=chunks, embedding=OpenAIEmbeddings(openai_api_key=OpenAI_API_Key))
    return vector_store

