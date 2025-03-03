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
PDF_Txt = config["PDF_Txt"]
OpenAI_API_Key = config["Openai_API_Key"]
Folder_Name = f"Book1-{PDF_Name}"

def collect_single_PDF_RAG_database():
    pdf_loader = PyMuPDFLoader(f"VerilogTextBooks/{PDF_Name}.pdf")
    documents = pdf_loader.load()
    print(len(documents))
    print(documents[0].page_content[0:100])
    print(documents[0].metadata)
    document = [documents[23]]
    text_splitter = RecursiveCharacterTextSplitter(chunk_size=1000, chunk_overlap=200)
    chunks = text_splitter.split_documents(document)
    for chunk in chunks:
        print(chunk.page_content)
        print("=======================")
    vector_store = Chroma.from_documents(documents=chunks, embedding=OpenAIEmbeddings(openai_api_key=OpenAI_API_Key))
    return vector_store


def collect_RAG_database():
    all_documents = []
    
    pdf_names = []

    with open(f"VerilogTextBooks/{PDF_Txt}") as file:
        pdf_names = file.readlines()

    pdf_names = [pdf_name.strip() for pdf_name in pdf_names]

    # Loop over each PDF name provided in the list
    for pdf_name in pdf_names:
        # Construct the file path for the current PDF
        file_path = f"VerilogTextBooks/{pdf_name}.pdf"
        pdf_loader = PyMuPDFLoader(file_path)
        
        # Load the documents (pages) from the current PDF
        documents = pdf_loader.load()
        all_documents.extend(documents)
        
        # Optional: Print information about the loaded document
        # print(f"Loaded {len(documents)} pages from {pdf_name}.pdf")
        # if documents:
        #     print("First 100 characters of first page:", documents[0].page_content[:100])
        #     print("Metadata:", documents[0].metadata)
    
    # Use a text splitter to break the combined documents into chunks
    text_splitter = RecursiveCharacterTextSplitter(chunk_size=1000, chunk_overlap=200)
    chunks = text_splitter.split_documents(all_documents)
    
    # Create the vector store from the document chunks
    vector_store = Chroma.from_documents(
        documents=chunks,
        embedding=OpenAIEmbeddings(openai_api_key=OpenAI_API_Key)
    )
    
    return vector_store


# collect_single_PDF_RAG_database()