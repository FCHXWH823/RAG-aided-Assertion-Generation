import pandas as pd
import os
import regex

dataset_dir = "Evaluation/Dataset/"

def remove_last_endmodule(verilog_code):
    lines = verilog_code.strip().split("\n")
    
    # Find the last occurrence of "endmodule"
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() == "endmodule":
            del lines[i]
            break  # Remove only the last occurrence

    return "\n".join(lines)




df = pd.read_csv("Evaluation/asserted-verilog-evaluation-dataset-transform.csv")

for i in range(len(df)):
    code = df.iloc[i]['code']
    master_module = df.iloc[i]['Master Module']
    fpv_dir = dataset_dir+master_module+"/"

    processed_code = remove_last_endmodule(code)
    processed_code += "\n\n"
    transformed_assertion = df.iloc[i]['transformed_assertion']
    processed_code += transformed_assertion
    processed_code += "\nendmodule\n"
    
    with open(fpv_dir+master_module+"_assertion.sv","w") as file:
        file.write(processed_code)
    


    


