import pandas as pd
import os
import re

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

    assertions = ""
    for assertion in lines_assertions:
        assertions += assertion + "\n"
    
    return assertions

def extract_csv_from_dataset(csv_name: str):
    
    df = pd.DataFrame(columns=["code","Master Module","assertion","FPV Script","link"])
    i = 0
    for folder in os.listdir("Evaluation/Dataset"):
        folder_path = os.path.join("Evaluation/Dataset/",folder)
        if os.path.isdir(folder_path):    
            master_module = folder
            fpv_dir = "Evaluation/Dataset/"+master_module+"/"

            with open(fpv_dir+master_module+"_assertion.sv","r") as file:
                verilog_code_w_assertions = file.read()
            
            with open(fpv_dir+master_module+".sv","r") as file:
                verilog_code_wo_assertions = file.read()

            with open(fpv_dir+"fpv.tcl","r") as file:
                fpv_tcl = file.read()

            with open(fpv_dir+"link.txt","r") as file:
                link = file.read()

            assertions = extract_verilog_code(verilog_code_w_assertions,verilog_code_wo_assertions)

            df.loc[i] = [verilog_code_wo_assertions,master_module,assertions,fpv_tcl,link]

            i += 1
    
    df.to_csv("Evaluation/"+csv_name)



    
        
    #     df_new.iloc[i]["code"] = verilog_code_wo_assertions
    #     df_new.iloc[i]["transformed_assertion"] = assertions
    #     df_new.iloc[i]["FPV Script"] = fpv_tcl

    # df_new.to_csv("Evaluation/asserted-verilog-evaluation-dataset-transform-new.csv")

# model = "deepseek-chat"
model = "ft:gpt-4o-mini-2024-07-18:nyuccs::BUh3lZyT"
methods = [""]
modified_model = "finetuned_gpt-4o-mini"

def modify_model_name():
    for folder in os.listdir("Evaluation/Dataset"):
        folder_path = os.path.join("Evaluation/Dataset/",folder)
        # os.system(f"rm {folder_path}/fpv__QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt")
        if os.path.isdir(folder_path):
            os.system(f"cp {folder_path}/{folder}_{model}.sv {folder_path}/{folder}_{modified_model}.sv")

def generate_fpv():

    for folder in os.listdir("Evaluation/Dataset"):
        folder_path = os.path.join("Evaluation/Dataset/",folder)
        # os.system(f"rm {folder_path}/fpv__QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt")
        if os.path.isdir(folder_path):
            with open(f"{folder_path}/fpv.tcl","r") as file:
                fpv_tcl = file.read()
            fpv_tcl_method = fpv_tcl.replace(f"./{folder}_assertion.sv",f"./{folder}_{modified_model}.sv").replace("fpv.rpt",f"fpv_{modified_model}.rpt")
            with open(f"{folder_path}/fpv_{modified_model}.tcl","w") as file:
                file.write(fpv_tcl_method)
            
            
            


if __name__ == '__main__':
    modify_model_name()
    generate_fpv()
    # extract_csv_from_dataset("evaluation-dataset.csv")

    



    


