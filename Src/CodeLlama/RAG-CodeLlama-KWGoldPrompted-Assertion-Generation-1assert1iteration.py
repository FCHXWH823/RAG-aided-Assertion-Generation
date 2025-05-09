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
from openai import OpenAI
from extract_keywords import *

from RAG_Database_New import *

from langchain_openai import ChatOpenAI
from langchain_ollama import ChatOllama

from json import JSONDecodeError

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

with open("Src/Config.yml") as file:
    config = yaml.safe_load(file)

PDF_Name = config["PDF_Name"]
Folder_Name = f"Book1-{PDF_Name}"
Model_Name = config["Model_Name"]
OpenAI_API_Key = config["Openai_API_Key"]
CodeLlama_Model_Name = config["CodeLlama_Model_Name"]
Excute_Folder = config["Excute_Folder"]
# Initialize embeddings
vector_store = collect_RAG_database()
retriever = vector_store.as_retriever()
# embeddings = OpenAIEmbeddings(openai_api_key=OpenAI_API_Key)
# vector_store = FAISS.load_local(f"RAG_Database/{Folder_Name}",embeddings,allow_dangerous_deserialization=True)

client = OpenAI(
        api_key=OpenAI_API_Key
)

# prompt
system_prompt = (
    "You are a helpful bot that generate the assertion satisfying some requirements for a given verilog code."
    "Use the following pieces of retrieved context to answer the question. "
    "\n\n"
    "{keywords_explaination}"
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

system_prompt_explain = (
    "You are a helpful bot that extract the used operators in the given systemverilog assertion."
    "The output format should be `[op1, op2, op3,...]`"
    "Use the following pieces of retrieved context to help answer the question. "
    "\n\n"
    "{context}"
)
prompt_explain = ChatPromptTemplate.from_messages(
    [
        ("system", system_prompt_explain),
        ("human","{input}"),
    ]
)

def assertion_format_prompt(llm_response, assertion_format):
    return f'''
    Please rewrite the following systemverilog assertion without changing its functionality:
    {llm_response}
    to STRICTLY follow the format:
    {assertion_format}
    Please ONLY output the rewritten one.  
    '''

# retriever = vector_store.as_retriever(search_kwargs={'k': 3})

# from langchain_openai import ChatOpenAI
# from langchain.chains import RetrievalQA

llm = ChatOllama(
    model = CodeLlama_Model_Name,
    temperature = 0.2,
    num_predict = 256
)

question_answer_chain = create_stuff_documents_chain(llm,prompt)
rag_chain = create_retrieval_chain(retriever,question_answer_chain)

question_answer_chain_checker = create_stuff_documents_chain(llm,prompt_checker)
rag_chain_checker = create_retrieval_chain(retriever,question_answer_chain_checker)

question_answer_chain_explain = create_stuff_documents_chain(llm,prompt_explain)
rag_chain_explain = create_retrieval_chain(retriever,question_answer_chain_explain)

results = retriever.invoke("in the past clock cycle.")

# results


# qa_chain = RetrievalQA.from_chain_type(llm, retriever=retriever)

def HybridRAG_SVAGeneration(assertion, details):
    explanation = details.get("Assertion Explaination", "No explanation provided")
    # clk_condition = "" if details.get("clock signal condition") is "none" else details.get("clock signal condition")
    # reset_condition = "" if details.get("disable condition") is "none" else details.get("disable condition")
    
    assertion_format = f"assert property (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff(...));"
    
    keywords = extract_keywords(explanation)
    extract_operators_explanations = extract_related_operators_of_keyword(keywords)
    
    checking_str = ""
    for op_explanation in extract_operators_explanations:
        checking_str += f"{op_explanation}\n\n"
        retrieved_doc = retriever.invoke(f"{op_explanation}")                    
        for doc in retrieved_doc:
            checking_str += doc.page_content + "\n\n"
        checking_str += "\n"    

    prompt = f"Given Verilog code snippet as below: \n{code}\n Please generate such a systemverilog assertion for it following the description:{explanation}. Ensure the syntax correctness and the used signals should be from the verilog code.\nThe output format should STRICTLY follow :\n{assertion_format}\nWITHOUT other things."

    llm_result = rag_chain.invoke({"keywords_explaination": checking_str, "code":code,"input":explanation,"assertion_format":assertion_format})
    llm_response = llm_result["answer"]
    
    # completion = client.chat.completions.create(
    # model= Model_Name,
    # messages=[
    #     {"role": "system", "content": "You are a helpful bot to modify the systemverilog assertion based on the given explanation."},
    #     {"role": "user", "content": f"Given the desired explanation\n{explanation},\n please check whether the systemverilog assertion {logic_expression} does not implement some events included in the explanation.\n"}
    # ]
    # )

    completion = client.chat.completions.create(
    model= OpenAI_Model_Name,
    messages=[
        {"role": "system", "content": "You are a helpful bot to extract the systemverilog assertion from the given text."},
        {"role": "user", "content": f"Please extract the systemverilog assertion from the following text and only output its logic expression without such as `assert property` and `@(posedge clk)`:\n{llm_response}"}
    ]
    )
    logic_expression = completion.choices[0].message.content
    
    # llm_explain = rag_chain_explain.invoke({"input":logic_expression})
    # llm_response_explain = llm_explain["answer"]

    # completion = client.chat.completions.create(
    # model= Model_Name,
    # messages=[
    #     {"role": "system", "content": "You are a helpful bot to break down the given systemverilog assertion and store them in an array. Only output the array in the format: `(p1, p2, p3,...)`."},
    #     {"role": "user", "content": f"{logic_expression}\n "}
    # ]
    # )
    # property_ops = completion.choices[0].message.content

    # property_ops = str(re.search(r'\((.*?)\)',property_ops,re.DOTALL).group(1)).split(',')

    checking_str = ""
    if "|=>" in logic_expression or "|->" in logic_expression:
        checking_str += "`|->`: \nif the left-hand side condition of |-> is true, the right-hand side condition of |-> is true in the same clock cycle\n\n\n"
        checking_str += "`|=>`: \nif the left-hand side condition of |=> is true, the right-hand side condition of |=> is true in the next one clock cycle\n\n\n"
    # read operators.json
    with open("operators.json","r") as file:
        operators = json.load(file)
    for op in operators:
        if op in logic_expression:
            checking_str += f"`{op}`: {operators[op]}\n\n"
            retrieved_doc = retriever.invoke(f"`{op}`: {operators[op]}")                    
            for doc in retrieved_doc:
                checking_str += doc.page_content + "\n\n"
            checking_str += "\n"    


    # checking_str += llm_response_explain

    llm_response = llm.invoke(input=[
        {"role": "system", "content": "You are a helpful bot to modify the systemverilog assertion based on the given explanation."},
        {"role": "user", "content": f"Given the desired explanation\n{explanation},\n please check whether the systemverilog assertion {logic_expression} operates with the correct logic and the same timing (i.e., clock cycle).\n The relevant context of the used operators are given:\n {checking_str}.\n If there exists, please list the differences and modify it into a new systemverilog assertion and output the new assertion.\n"}
    ]).content

    rewrite_prompt = assertion_format_prompt(llm_response,assertion_format)
    completion = client.chat.completions.create(
        model= OpenAI_Model_Name,
        messages=[
        {"role": "system", "content": "You are a helpful bot that rewrite the input to follow the specified format."},
        {"role": "user", "content": rewrite_prompt}
    ])
    llm_response = completion.choices[0].message.content

    # # assertion checker
    # nItChecker = 3
    # for it in range(nItChecker):
    #     checker_prompt = assertion_checker_prompt(llm_response,assertion_format)
    #     llm_response = rag_chain_checker.invoke({"input":checker_prompt})["answer"]

    return llm_response

# Run a query
with open(f'Results/RAG-Openai-4o-mini-Prompted-Assertion-Generation-Results-{PDF_Name}-for-New-Dataset.csv', 'w', newline='') as csv_file:
    csv_writer = csv.writer(csv_file)
    csv_writer.writerow(['Master Module','Code','golden_assertions','llm_assertions'])
    for folder in os.listdir("Evaluation/Dataset/"):
        if Excute_Folder != 'ALL_DESIGNS' and Excute_Folder not in folder:
            continue
        if folder in ["Ripple_Carry_Adder", "or1200_operandmuxes", "gray", "Flip_Flop_Array", "PSGBusArb", "apb", "host_interface", "control_unit", "Programmable_Sequence_Detector", "PWM", "module_i2c", "delay2", "simple_req_ack", "Gray_Code_Counter", "uartTrans", "i2c", "uartRec", "APB_FSM_Controller", "register", "SEVEN","arbiter","simple_pipeline","lcd","Parallel_In_Serial_Out_Shift_Reg","fifo","or1200_if","uart_transmit","ff","Gray_To_Binary","delay","BusArbiter"]:
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
                i += 1

                while True:
                    llm_response = HybridRAG_SVAGeneration(assertion, details)
                    match = re.search(r'assert property\s*\(\s*(.*?)\s*\)\s*;', llm_response, re.DOTALL)
                    if match is None:
                        continue
                    matched_str = str(match.group(0))
                    matched_str = matched_str.replace("\n"," ")
                    test_str = "{\n"
                    test_str += f"\"Assertion {i}\": \"{matched_str}\""
                    test_str += "\n}"
                    try:
                        json_test_str = json.loads(test_str)
                    except JSONDecodeError:
                        continue
                    else:
                        llm_responses.append(f"\"Assertion {i}\": \"{matched_str}\"") 
                        break

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

                with open(folder_path+"/"+folder+f"_KWGoldHybridRAG-{CodeLlama_Model_Name}.sv","w") as file:
                    file.write(processed_code)

