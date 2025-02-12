from langchain_community.document_loaders import PyMuPDFLoader
import pandas as pd
import csv
import os
from langchain_openai import OpenAIEmbeddings
from langchain_community.vectorstores import FAISS
import yaml
import json
import re

from langchain.chains.retrieval import create_retrieval_chain
from langchain.chains.combine_documents import create_stuff_documents_chain
from langchain_core.prompts import ChatPromptTemplate
from langchain_openai import ChatOpenAI


from RAG_Database_New import *

def assertion_checker_prompt(llm_response, assertion_format):
    return f'''
    Please correct the following systemverilog assertion if there exist some syntax errors in it, such as unmatched parentheses:
    {llm_response}
    Please output the corrected assertion STRICTLY in the following format:
    {assertion_format}
    '''

def remove_last_endmodule(verilog_code):
    lines = verilog_code.strip().split("\n")
    
    # Find the last occurrence of "endmodule"
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() == "endmodule":
            del lines[i]
            break  # Remove only the last occurrence

    return "\n".join(lines)

with open("Src/Config.yml") as file:
    config = yaml.safe_load(file)

PDF_Name = config["PDF_Name"]
Folder_Name = f"Book1-{PDF_Name}"

OpenAI_API_Key = config["Openai_API_Key"]
# Initialize embeddings
vector_store = collect_RAG_database()
retriever = vector_store.as_retriever()
# embeddings = OpenAIEmbeddings(openai_api_key=OpenAI_API_Key)
# vector_store = FAISS.load_local(f"RAG_Database/{Folder_Name}",embeddings,allow_dangerous_deserialization=True)


# prompt
system_prompt = (
    "You are a helpful bot that generate the assertion satisfying some requirements for a given verilog code."
    "Use the following pieces of retrieved context to answer the question. "
    "\n\n"
    "{context}"
)
prompt = ChatPromptTemplate.from_messages(
    [
        ("system", system_prompt),
        ("human","{input}"),
    ]
)


# retriever = vector_store.as_retriever(search_kwargs={'k': 3})

# from langchain_openai import ChatOpenAI
# from langchain.chains import RetrievalQA

llm = ChatOpenAI(
    model="gpt-4o-mini-2024-07-18",
    # model="o3-mini",
    api_key=OpenAI_API_Key
    )

question_answer_chain = create_stuff_documents_chain(llm,prompt)
rag_chain = create_retrieval_chain(retriever,question_answer_chain)

# results = rag_chain.invoke({"input": "Please explain different types of assertions."})

# results


# qa_chain = RetrievalQA.from_chain_type(llm, retriever=retriever)

# Run a query
with open(f'Results/RAG-Openai-4o-mini-Prompted-Assertion-Generation-Results-{PDF_Name}-for-New-Dataset.csv', 'w', newline='') as csv_file:
    csv_writer = csv.writer(csv_file)
    csv_writer.writerow(['Master Module','Code','golden_assertions','llm_assertions'])
    for folder in os.listdir("Evaluation/Dataset/"):
        folder_path = os.path.join("Evaluation/Dataset/",folder)
        if os.path.isdir(folder_path):
            with open(folder_path+"/"+folder+".sv","r") as file:
                code = file.read()
            with open(folder_path+"/explanation.json") as file:
                # explanation_origin = file.read()
                explanation_json = json.load(file)

            with open(folder_path+"/explanation.json") as file:
                explanation_origin = file.read()
            
            i = 0

            llm_responses = []
            for assertion, details in explanation_json.items():
                explanation = details.get("Assertion Explaination", "No explanation provided")
                # clk_condition = "" if details.get("clock signal condition") is "none" else details.get("clock signal condition")
                # reset_condition = "" if details.get("disable condition") is "none" else details.get("disable condition")
                
                assertion_format = f"assert property (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff(...));"
                

                prompt = f"Given Verilog code snippet as below: \n{code}\n Please generate such an assertion for it following the description:{explanation}\nThe output format should STRICTLY follow :\n{assertion_format}\nWITHOUT other things."

                llm_response = rag_chain.invoke({"input":prompt})["answer"]

                # assertion checker
                nItChecker = 3
                for it in range(nItChecker):
                    checker_prompt = assertion_checker_prompt(llm_response,assertion_format)
                    llm_response = rag_chain.invoke({"input":prompt})["answer"]

                i += 1
                match = re.search(r'assert property\s*\(\s*(.*?)\s*\)\s*;', llm_response, re.DOTALL)
                matched_str = str(match.group(0))
                matched_str = matched_str.replace("\n"," ")
                llm_responses.append(f"\"Assertion {i}\": \"{matched_str}\"") 

            llm_response = "{\n"
            for i in range(len(llm_responses)-1):
                llm_response += llm_responses[i]+",\n"
            llm_response +=llm_responses[-1]+"\n}"
            csv_writer.writerow([folder,code,explanation_origin,llm_response])

            if config["JasperGold_VERIFY"] == 1:
                llm_assertions = json.loads(llm_response)
                clk_conditions = []
                disable_conditions = []
                golden_logic_expressions = []
                llm_logic_expressions = []

                for assertion, details in explanation_json.items():
                    clk_condition = "" if details.get("clock signal condition") == "none" else details.get("clock signal condition")
                    disable_condition = "" if details.get("disable condition") == "none" else details.get("disable condition")
                    logic_expression = details.get("logical expression")
                    clk_conditions.append(clk_condition)
                    disable_conditions.append(disable_condition)
                    golden_logic_expressions.append(logic_expression)
                    
                for assertion, details in llm_assertions.items():
                    match = re.search(r'assert property\s*\(\s*(.*?)\s*\)\s*;', details)
                    llm_logic_expressions.append(match.group(1) if match else "")
                
                combine_assertions = []
                for i in range(len(clk_conditions)):
                    combine_assertion = f"assert property ({clk_conditions[i]} {disable_conditions[i]} ({llm_logic_expressions[i]}));" 
                    combine_assertions.append(combine_assertion)
                    combine_assertion = f"assert property ({clk_conditions[i]} {disable_conditions[i]} ({golden_logic_expressions[i]}) iff ({llm_logic_expressions[i]}));" 
                    combine_assertions.append(combine_assertion)
                    

                processed_code = remove_last_endmodule(code)
                processed_code += "\n\n"
                for assertion in combine_assertions:
                    processed_code += assertion+"\n"
                processed_code += "\nendmodule\n"

                with open(folder_path+"/"+folder+"_Openai-4o-mini.sv","w") as file:
                    file.write(processed_code)

