import os
import json
import sys


# use a dict to store the operators and corresponding explanations
operatosrs = {}

for folder in os.listdir("Evaluation/Dataset/"):
    folder_path = os.path.join("Evaluation/Dataset/",folder)
    
    
    if os.path.isdir(folder_path):
        print(f"===================== Processing folder: {folder} ====================")
        # read the json file in the folder
        with open(folder_path+"/explanation.json","r") as file:
            data = json.load(file)

        # get the Logical Operators and corresponding Explanations of each assertion
        for key in data:
            ops = data[key]["Logical Operators"]
            ops_explanation = data[key]["Logical Operators Explanation"]
            for op in ops:
                if op not in operatosrs:
                    operatosrs[op] = ops_explanation[op]
        
        print(f"============================={folder}-Openai-4o-mini finished")

for key, value in operatosrs.items():
    print(f"{key}: {value}")
# write the operators and explanations to a json file
with open("operators.json","w") as file:
    json.dump(operatosrs,file,indent=4)