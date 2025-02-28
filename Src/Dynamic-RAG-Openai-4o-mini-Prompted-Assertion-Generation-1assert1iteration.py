import os
from langchain.embeddings import OpenAIEmbeddings
from langchain.vectorstores import Chroma
from langchain.docstore.document import Document
from PyMuPDF import *
import yaml
from langchain.chains.retrieval import create_retrieval_chain
from langchain.chains.combine_documents import create_stuff_documents_chain
from langchain.retrievers.multi_query import MultiQueryRetriever
from langchain_core.prompts import ChatPromptTemplate
from langchain_openai import ChatOpenAI
import json
import csv
import re


with open("Src/Config.yml") as file:
    config = yaml.safe_load(file)
# Load your PDFs
# PDF_Name = "CernyDudani-SVA- The Power of Assertions in SystemVerilog"
PDF_Name = config["PDF_Name"]
PDF_Txt = config["PDF_Txt"]
OpenAI_API_Key = config["Openai_API_Key"]
Folder_Name = f"Book1-{PDF_Name}"
Model_Name = config["Model_Name"]
# def build_rag_system(pdf_path):
#     """
#     1. Extract code blocks and text blocks from the PDF.
#     2. Store code blocks in a 'code_db' (Chroma).
#     3. Store text blocks in a 'text_db' (Chroma).
#     4. Return the two vector stores for retrieval.
#     """
#     # 1) Get all blocks from PDF
#     blocks = get_pdf_blocks(pdf_path)

#     # 2) Separate code vs. text
#     code_docs = []
#     text_docs = []
#     for idx, block in enumerate(blocks):
#         content = block_to_text(block)
#         # Create a LangChain "Document" object with page_content plus metadata
#         if block["type"] == "code":
#             last_content = "" if idx == 0 else block_to_text(blocks[idx-1])
#             next_content = "" if idx == len(blocks)-1 else block_to_text(blocks[idx+1])
#             content = f"{last_content}\n\n{content}\n\n{next_content}"
#             print(content+"\n-----------------------\n\n")
#         doc = Document(page_content=content, metadata={"type": block["type"], "block_index": idx})
#         if block["type"] == "code":
#             code_docs.append(doc)
#         else:
#             text_docs.append(doc)

#     # 3) Build embeddings
#     embedding_fn = OpenAIEmbeddings(openai_api_key=OpenAI_API_Key)  # or HuggingFaceEmbeddings(), etc.

#     # 4) Create code vector store
#     code_db = Chroma.from_documents(code_docs, embedding=embedding_fn, collection_name="code_blocks")

#     # 5) Create text vector store
#     text_db = Chroma.from_documents(text_docs, embedding=embedding_fn, collection_name="text_blocks")

#     return code_db, text_db


def build_rag_system():
    """
    1. Extract code blocks and text blocks from the PDF.
    2. Store code blocks in a 'code_db' (Chroma).
    3. Store text blocks in a 'text_db' (Chroma).
    4. Return the two vector stores for retrieval.
    """
    pdf_names = []

    with open(f"VerilogTextBooks/{PDF_Txt}") as file:
        pdf_names = file.readlines()

    pdf_names = [pdf_name.strip() for pdf_name in pdf_names]

    # Loop over each PDF name provided in the list
    blocks = []
    for pdf_name in pdf_names:
        # Construct the file path for the current PDF
        pdf_path = f"VerilogTextBooks/{pdf_name}.pdf"
    # 1) Get all blocks from PDF
        blocks += get_pdf_blocks(pdf_path)

    # 2) Separate code vs. text
    code_docs = []
    text_docs = []
    for idx, block in enumerate(blocks):
        content = block_to_text(block)
        # Create a LangChain "Document" object with page_content plus metadata
        if block["type"] == "code":
            last_content = "" if idx == 0 else block_to_text(blocks[idx-1])
            next_content = "" if idx == len(blocks)-1 else block_to_text(blocks[idx+1])
            content = f"{last_content}\n\n{content}\n\n{next_content}"
            print(content+"\n-----------------------\n\n")
        doc = Document(page_content=content, metadata={"type": block["type"], "block_index": idx})
        if block["type"] == "code":
            code_docs.append(doc)
        else:
            text_docs.append(doc)

    # 3) Build embeddings
    embedding_fn = OpenAIEmbeddings(openai_api_key=OpenAI_API_Key)  # or HuggingFaceEmbeddings(), etc.

    # 4) Create code vector store
    code_db = Chroma.from_documents(code_docs, embedding=embedding_fn, collection_name="code_blocks")

    # 5) Create text vector store
    text_db = Chroma.from_documents(text_docs, embedding=embedding_fn, collection_name="text_blocks")

    return code_db, text_db
 

code_store, text_store = build_rag_system()

code_retriever = code_store.as_retriever()
text_retriever = text_store.as_retriever()

# prompt
system_prompt = (
    "You are a helpful bot that generate the assertion satisfying some requirements for a given verilog code."
    "Use the following pieces of retrieved context to help answer the question. "
    "\n\n"
    "{context}"
)
prompt = ChatPromptTemplate.from_messages(
    [
        ("system", system_prompt),
        ("human","Given Verilog code snippet as below: \n{code}\n Please generate such an assertion for it following the description:{input}\nThe output format should STRICTLY follow :\n{assertion_format}\nWITHOUT other things."),
    ]
)

system_prompt_checker = (
    "You are a helpful bot that check the syntax correctness of the given assertion and corret it if there exist syntaxs error."
    "Use the following pieces of retrieved context to help answer the question. "
    "\n\n"
    "{context}"
)
prompt_checker = ChatPromptTemplate.from_messages(
    [
        ("system", system_prompt_checker),
        ("human","{input}"),
    ]
)

# retriever = vector_store.as_retriever(search_kwargs={'k': 3})

# from langchain_openai import ChatOpenAI
# from langchain.chains import RetrievalQA

llm = ChatOpenAI(
    model=Model_Name,
    # model="o3-mini",
    api_key=OpenAI_API_Key
    )

question_answer_chain = create_stuff_documents_chain(llm,prompt)
rag_chain = create_retrieval_chain(code_retriever,question_answer_chain)

question_answer_chain_checker = create_stuff_documents_chain(llm,prompt_checker)
rag_chain_checker = create_retrieval_chain(code_retriever,question_answer_chain_checker)


# query_from_llm = MultiQueryRetriever.from_llm(
#     retriever=text_retriever, llm=llm
# )
# question = "Show me the usage of the always block in the code"


# llm_response = rag_chain.invoke({"input":question})

# llm_response

def assertion_checker_prompt(llm_response, assertion_format):
    return f'''
    Please correct the following systemverilog assertion if there exist some syntax errors in it, such as unmatched parentheses:
    {llm_response}
    Please output the corrected assertion STRICTLY in the following format:
    {assertion_format}
    '''

def extract_last_module(verilog_code: str) -> str:
    """
    Extract the last Verilog module from the given Verilog code string.
    
    Parameters:
        verilog_code (str): A string containing the Verilog code.
    
    Returns:
        str: The last module found in the code, or an empty string if no module is found.
    """
    # Use a regex pattern with non-greedy matching to capture each module block.
    # The pattern looks for a word boundary followed by 'module', then matches until
    # the first occurrence of 'endmodule' (also at a word boundary).
    pattern = r'\b(module\b.*?\bendmodule\b)'
    
    # Use DOTALL so that the dot (.) matches newline characters.
    modules = re.findall(pattern, verilog_code, flags=re.DOTALL)
    
    if modules:
        return modules[-1].strip()
    else:
        return ""

def extract_prerequist_of_assertions(verilog_code_w_assertions:str, verilog_code_wo_assertions:str, num_assertions: int):
    lines_w_assertions = extract_last_module(verilog_code_w_assertions).strip().split("\n")

    lines_wo_assertions = extract_last_module(verilog_code_wo_assertions).strip().split("\n")

    lines_assertions = lines_w_assertions[len(lines_wo_assertions):len(lines_w_assertions)-1]

    # lines_prerequist = lines_assertions[:-num_assertions]
    lines_assertions.append("// above are golden assertions")
    return lines_assertions

def remove_last_endmodule(verilog_code):
    lines = verilog_code.strip().split("\n")
    
    # Find the last occurrence of "endmodule"
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() == "endmodule":
            del lines[i]
            break  # Remove only the last occurrence

    return "\n".join(lines)


with open(f'Results/Dynamic-RAG-Openai-4o-mini-Prompted-Assertion-Generation-Results-{PDF_Name}-for-New-Dataset.csv', 'w', newline='') as csv_file:
    csv_writer = csv.writer(csv_file)
    csv_writer.writerow(['Master Module','Code','golden_assertions','llm_assertions'])
    for folder in os.listdir("Evaluation/Dataset/"):
        if "a25_wishbone" not in folder:
            continue
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
                explanation = details.get("Assertion Explaination", "No explanation provided").lower()

                # clk_condition = "" if details.get("clock signal condition") is "none" else details.get("clock signal condition")
                # reset_condition = "" if details.get("disable condition") is "none" else details.get("disable condition")
                
                assertion_format = f"assert property (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff(...));"
                

                prompt = f"Given Verilog code snippet as below: \n{code}\n Please generate such an assertion for it following the description:{explanation}\nThe output format should STRICTLY follow :\n{assertion_format}\nWITHOUT other things."

                llm_result = rag_chain.invoke({"code":code,"input":explanation,"assertion_format":assertion_format})
                llm_response = llm_result["answer"]

                # assertion checker
                nItChecker = 3
                for it in range(nItChecker):
                    checker_prompt = assertion_checker_prompt(llm_response,assertion_format)
                    llm_response = rag_chain_checker.invoke({"input":checker_prompt})["answer"]

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

            print(f"====================={folder} finished=====================")

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
                with open(folder_path+"/"+folder+".sv","r") as file:
                    verilog_code_wo_assertions = file.read()
                with open(folder_path+"/"+folder+"_assertion.sv","r") as file:
                    verilog_code_w_assertions = file.read()
                
                # combine_assertions = remove_last_endmodule(verilog_code_w_assertions)
                # combine_assertions = extract_prerequist_of_assertions(verilog_code_w_assertions,verilog_code_wo_assertions,len(clk_conditions))

                for i in range(len(clk_conditions)):
                    combine_assertion = f"assert property ({clk_conditions[i]} {disable_conditions[i]} ({llm_logic_expressions[i]}));" 
                    combine_assertions.append(combine_assertion)
                    combine_assertion = f"assert property ({clk_conditions[i]} {disable_conditions[i]} ({golden_logic_expressions[i]}) iff ({llm_logic_expressions[i]}));" 
                    combine_assertions.append(combine_assertion)
                    

                processed_code = remove_last_endmodule(verilog_code_w_assertions)
                processed_code += "\n\n"
                for assertion in combine_assertions:
                    processed_code += assertion+"\n"
                processed_code += "\nendmodule\n"

                with open(folder_path+"/"+folder+"_Dynamic-RAG-Openai-4o-mini.sv","w") as file:
                    file.write(processed_code)






