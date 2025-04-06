import os
import json
import sys
import yaml
from openai import OpenAI

with open("Src/Config.yml") as file:
    config = yaml.safe_load(file)
# Load your PDFs
OpenAI_API_Key = config["Openai_API_Key"]
Model_Name = "gpt-4o-mini"

client = OpenAI(
        api_key=OpenAI_API_Key
)

# use a dict to store the operators and corresponding explanations
# operatosrs = {}

# for folder in os.listdir("Evaluation/Dataset/"):
#     folder_path = os.path.join("Evaluation/Dataset/",folder)
    
    
#     if os.path.isdir(folder_path):
#         print(f"===================== Processing folder: {folder} ====================")
#         # read the json file in the folder
#         with open(folder_path+"/explanation.json","r") as file:
#             data = json.load(file)

#         # get the Logical Operators and corresponding Explanations of each assertion
#         for key in data:
#             ops = data[key]["Logical Operators"]
#             ops_explanation = data[key]["Logical Operators Explanation"]
#             for op in ops:
#                 if op not in operatosrs:
#                     operatosrs[op] = ops_explanation[op]
        
#         print(f"============================={folder}-Openai-4o-mini finished")

# for key, value in operatosrs.items():
#     print(f"{key}: {value}")
# # write the operators and explanations to a json file
# with open("operators.json","w") as file:
#     json.dump(operatosrs,file,indent=4)

import re

def parse_numbered_output(text):
    """
    Parses a numbered list in the format [n]. text and extracts each item.

    Args:
        text (str): The multiline string output.

    Returns:
        List[str]: A list of extracted parts in order.
    """
    # Pattern to match [1]. ..., [2]. ..., etc.
    lines = text.splitlines()
    outputs = []
    for line in lines:
        # get the content 1. ...
        pattern = r"^\d+\.\s+(.*)"
        match = re.match(pattern, line)
        if match:
            outputs.append(match.group(1).strip())
    return outputs


# use embedding=OpenAIEmbeddings(openai_api_key=OpenAI_API_Key) to get the embedding of the expalanations
from langchain.vectorstores import Chroma
from langchain.docstore.document import Document
from langchain.embeddings import OpenAIEmbeddings

# read the json file and print the operators and explanations
with open("operators.json","r") as file:
    data = json.load(file)
    explanation_docs = []
    ops_explanation = ""
    for key, value in data.items():
        ops_explanation += f"{key}: {value}\n"
        # op = key
        # op_explanation = value
        # doc = Document(page_content=op_explanation, metadata={"op": op})
        # explanation_docs.append(doc)
    
    nl_sva = "when the third bit of grant output is asserted and in the previous clock cycle the arbitration type selector signal was equal to 1, then in the previous clock cycle the third bit of request input signal must be asserted and the first and second bits of request input signal must not be asserted from the current clock cycle"
    prompt_split = f"Split the following sentence\n{nl_sva}\n into multiple parts, each representing an operation over a single signal or group of signals. Present the output as a numbered list in the following format:\n1. <First operation>\n2. <Second operation>\n3. <Third operation>\n...\n"
    completion = client.chat.completions.create(
                model= Model_Name,
                messages=[
                    {"role": "system", "content": "You are a helpful bot to split a given sentence into multiple parts."},
                    {"role": "user", "content": prompt_split}
                ]
    )
    
    print("Split Results: ", completion.choices[0].message.content)

    parsed = parse_numbered_output(completion.choices[0].message.content)
    for i, part in enumerate(parsed, 1):
        
    
        keyword = part
        prompt = f"Given a set of systemverilog assertion operatosrs and their explanations as follows:\n {ops_explanation}\n Please extract the most relevant operator from the natural language input \n`{keyword}`\n, but do not return anything if no relevant operator exists。\n"
        completion = client.chat.completions.create(
                    model= Model_Name,
                    messages=[
                        {"role": "system", "content": "You are a helpful bot to extract the relevant systemverilog assertion operator from a given list."},
                        {"role": "user", "content": prompt}
                    ]
        )
        # embedding_fn = OpenAIEmbeddings(openai_api_key=OpenAI_API_Key)
        # ops_explanation_db = Chroma.from_documents(explanation_docs, embedding=embedding_fn, collection_name="ops_explanations")
        # ops_explanation_retriever = ops_explanation_db.as_retriever(search_kwargs={"k": 1, "score_threshold": 0.7},search_type="similarity_score_threshold")

        # results = ops_explanation_retriever.invoke("Third bit of req signal (bit 2) must be asserted")

        
        print("Results: ", completion.choices[0].message.content)



