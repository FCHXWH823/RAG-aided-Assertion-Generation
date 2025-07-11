import pandas as pd
import os
import re
import json
from docker_vcs import *

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

def remove_last_endmodule(verilog_code):
    lines = verilog_code.strip().split("\n")
    
    # Find the last occurrence of "endmodule"
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() == "endmodule":
            del lines[i]
            break  # Remove only the last occurrence

    return "\n".join(lines)

def extract_verilog_code(verilog_code_w_assertions:str, verilog_code_wo_assertions:str):
    lines_w_assertions = extract_last_module(verilog_code_w_assertions).strip().split("\n")

    lines_wo_assertions = extract_last_module(verilog_code_wo_assertions).strip().split("\n")

    lines_assertions = lines_w_assertions[len(lines_wo_assertions):len(lines_w_assertions)-1]

    return lines_assertions[:-1]

if __name__ == '__main__':
#     for folder in os.listdir("/scratch/wx2356/Hybrid-NL2SVA/RAG-aided-Assertion-Generation/Evaluation/Dataset"):
        folder = "a25_wishbone"
        folder_path = os.path.join("/scratch/wx2356/Hybrid-NL2SVA/RAG-aided-Assertion-Generation/Evaluation/Dataset",folder)
        if os.path.isdir(folder_path):
            master_module = folder
            fpv_dir = "/scratch/wx2356/Hybrid-NL2SVA/RAG-aided-Assertion-Generation/Evaluation/Dataset/"+master_module+"/"
            leaf_sv_files = []
            print("leaf_sv_files:", leaf_sv_files)
            with open(folder_path+"/explanation.json") as file:
                explanation_json = json.load(file)
            for assertion, details in explanation_json.items():
                if "Assertion" not in assertion:
                    leaf_sv_files = details
            with open(fpv_dir+master_module+".sv","r") as file:
                 verilog_code_wo_assertions = file.read()
            
            with open(fpv_dir+master_module+"_assertion.sv","r") as file:
                 verilog_code_w_goldassertions = file.read()
            
            with open(fpv_dir+master_module+"_deepseek-coder-7b-finetune-nl2sva-prompt-guided.sv","r") as file:
                 verilog_code_w_assertions = file.read()
            
            if len(leaf_sv_files):
                 leaf_file_name = leaf_sv_files[0]
                 with open(folder_path+"/"+leaf_sv_files[0]+".v","r") as file:
                     verilog_leaf_sv = file.read()
            else:
                 verilog_leaf_sv = ""
                 leaf_file_name = ""

            svas = extract_verilog_code(verilog_code_w_assertions,verilog_code_w_goldassertions)
            print(len(svas))
            for sva in svas:
                print(sva)
                print("-----")
            i = 0
            svas_processed = []
            for sva in svas:
                 if i % 2 == 1:
                     i += 1         
                     continue             
                 sc_detect = vcs_process(verilog_leaf_sv, verilog_code_wo_assertions, sva, leaf_file_name, f"{folder}_{int(i/2)}_llm")
                 print("SC detected:", sc_detect)
                 if sc_detect:
                     svas_processed.append("// " + svas[i])
                     svas_processed.append("// " + svas[i+1])
                 i += 1
            processed_code = remove_last_endmodule(verilog_code_w_goldassertions)
            processed_code += "\n\n"
            for assertion in svas_processed:
                processed_code += assertion+"\n"
            processed_code += "\nendmodule\n"

            with open(fpv_dir+master_module+"_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv","w") as file:
                file.write(processed_code)

