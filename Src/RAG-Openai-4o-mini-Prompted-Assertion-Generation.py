from langchain_community.document_loaders import PyMuPDFLoader
import pandas as pd
import csv
from langchain_openai import OpenAIEmbeddings
from langchain_community.vectorstores import FAISS

PDF_Name = "CernyDudani-SVA- The Power of Assertions in SystemVerilog"
Folder_Name = f"Book1-{PDF_Name}"
# Initialize embeddings
embeddings = OpenAIEmbeddings(openai_api_key="")
vector_store = FAISS.load_local(f"RAG_Database/{Folder_Name}",embeddings,allow_dangerous_deserialization=True)

retriever = vector_store.as_retriever(search_kwargs={'k': 3})

# from langchain.llms import OpenAI
from langchain_openai import ChatOpenAI
from langchain.chains import RetrievalQA

llm = ChatOpenAI(
    model="gpt-4o-mini-2024-07-18",
    api_key=""
    )

qa_chain = RetrievalQA.from_chain_type(llm, retriever=retriever)

df = pd.read_csv('Evaluation/prompted-assertion-generation-dataset.csv')
# Run a query
with open('Results/RAG-Openai-4o-mini-Prompted-Assertion-Generation-Results.csv', 'w', newline='') as csv_file:
    csv_writer = csv.writer(csv_file)
    csv_writer.writerow(['code','HumanExplanation','pure code','prompt','llm_response'])
    for id in range(len(df)):
        code = df.iloc[id]['code']
        humanexplanation = df.iloc[id]['HumanExplanation']
        purecode = df.iloc[id]['pure code']
        prompt = f"Given Verilog code snippet as below: \n{purecode}\n Please generate a rewritten version of it, which contains several useful assertions and each of them follows a description as follows:{humanexplanation}\n"
        

        llm_response = qa_chain.run(prompt)

        csv_writer.writerow([code,humanexplanation,purecode,prompt,llm_response])
