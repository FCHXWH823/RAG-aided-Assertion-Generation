from langchain_community.document_loaders import PyMuPDFLoader
import pandas as pd
import csv
from langchain_openai import OpenAIEmbeddings
from langchain_community.vectorstores import FAISS
import yaml

PDF_Name = "CernyDudani-SVA- The Power of Assertions in SystemVerilog"
Folder_Name = f"Book1-{PDF_Name}"

with open("Src/Config.yml") as file:
    config = yaml.safe_load(file)

OpenAI_API_Key = config["Openai_API_Key"]
# Initialize embeddings
embeddings = OpenAIEmbeddings(openai_api_key=OpenAI_API_Key)
vector_store = FAISS.load_local(f"RAG_Database/{Folder_Name}",embeddings,allow_dangerous_deserialization=True)

retriever = vector_store.as_retriever(search_kwargs={'k': 3})

# from langchain.llms import OpenAI
from langchain_openai import ChatOpenAI
from langchain.chains import RetrievalQA

llm = ChatOpenAI(
    model="gpt-4o-mini-2024-07-18",
    api_key=OpenAI_API_Key
    )

qa_chain = RetrievalQA.from_chain_type(llm, retriever=retriever)

df = pd.read_csv('asserted-verilog-evaluation-dataset.csv')
# Run a query
with open('Langchain-RAG-eval-results.csv', 'a', newline='') as csv_file:
    csv_writer = csv.writer(csv_file)
    # csv_writer.writerow(['code','HumanExplanation','pure code','prompt','llm_response'])
    for id in range(25, len(df)):
        code = df.iloc[id]['code']
        humanexplanation = df.iloc[id]['HumanExplanation']
        purecode = df.iloc[id]['pure code']
        prompt = "Given Verilog code snippet as below: \n" + purecode + "\n Please generate a rewritten version of it, which contains some useful assertions for verification. \n"
        

        llm_response = qa_chain.run(prompt)

        csv_writer.writerow([code,humanexplanation,purecode,prompt,llm_response])
