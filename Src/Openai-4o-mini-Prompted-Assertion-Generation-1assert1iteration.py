from openai import OpenAI
import pandas as pd
import csv
import random
import yaml
import os
import json
import re
#client = OpenAI()


def remove_last_endmodule(verilog_code):
    lines = verilog_code.strip().split("\n")
    
    # Find the last occurrence of "endmodule"
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() == "endmodule":
            del lines[i]
            break  # Remove only the last occurrence

    return "\n".join(lines)

def init_prompt_template_completion(model_id,code):
    return client.chat.completions.create(
        model=model_id,
        messages=[
            {"role": "system", "content": "You are a helpful bot that provides a brief explanation of the input code."},
            {"role": "user", "content": "Given input code snippet as below: \n" + code + "\n Please give a brief explanation of the code. \n"}
        ]
    )

with open("Src/Config.yml") as file:
    config = yaml.safe_load(file)

OpenAI_API_Key = config["Openai_API_Key"]

client = OpenAI(
        api_key=OpenAI_API_Key
)

#model_name = "ft:gpt-3.5-turbo-0125:personal::A9KbE7Vx"
# initial key
# model_name_1 = "ft:gpt-4o-mini-2024-07-18:personal::ADG5sJhx" # initial prompt template ,epoch: 1
# model_name_2 = "ft:gpt-4o-mini-2024-07-18:personal::ADOVxQ34" # initial prompt template, epoch: 2
# model_name_3 = "ft:gpt-4o-mini-2024-07-18:personal::ADRj5YX0" # new prompt template, epoch: 1
# model_name_4 = "ft:gpt-4o-mini-2024-07-18:personal::ADYuwFrD" # initial prompt template, epoch: 10
# model_name_5 = "ft:gpt-4o-mini-2024-07-18:personal::ADefsoKl" # new prompt template, epoch: 10

with open("Evaluation/Dataset/Ripple_Carry_Adder/explanation.json") as jsonfile:
    data = json.load(jsonfile)

# NYU CCS's key
model_name = "gpt-4o-mini-2024-07-18"
# model_name = "o3-mini"

eval_num = 100
with open('Results/Openai-4o-mini-Prompted-Assertion-Generation-Results-for-New-Dataset.csv', 'w', newline='') as csv_file:
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
                
                assertion_format = f"assert property (ONLY logical_expression without_clock signal condition @(...) and WITHOUT disable condition disable iff(...));"
                

                prompt = f"Given Verilog code snippet as below: \n{code}\n Please generate such an assertion for it following the description:{explanation}\nThe output format should STRICTLY follow :\n{assertion_format}\nWITHOUT other things."

                completion = client.chat.completions.create(
                model=model_name,
                messages=[
                    {"role": "system", "content": "You are a helpful bot that generate the assertion satisfying some requirements for a given verilog code."},
                    {"role": "user", "content": prompt}
                ]
                )

                i += 1
                match = re.search(r'assert property \(.*\);', completion.choices[0].message.content, re.DOTALL)
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
                    match = re.search(r'assert property\s*\(\s*(.*?)\s*\)', details)
                    llm_logic_expressions.append(match.group(1) if match else "")
                
                combine_assertions = []
                for i in range(len(clk_conditions)):
                    combine_assertion = f"assert property ({clk_conditions[i]} {disable_conditions[i]} ({golden_logic_expressions[i]}) iff ({llm_logic_expressions[i]}));" 
                    combine_assertions.append(combine_assertion)

                processed_code = remove_last_endmodule(code)
                processed_code += "\n\n"
                for assertion in combine_assertions:
                    processed_code += assertion+"\n"
                processed_code += "\nendmodule\n"

                with open(folder_path+"/"+folder+"_Openai-4o-mini.sv","w") as file:
                    file.write(processed_code)





                



            
            

# with open('Results/Openai-4o-mini-Prompted-Assertion-Generation-Results.csv', 'w', newline='') as csv_file:
#     csv_writer = csv.writer(csv_file)
#     csv_writer.writerow(['code','HumanExplanation','pure code','prompt','llm_response'])
#     for id in range(len(df)):
#         code = df.iloc[id]['code']
#         humanexplanation = df.iloc[id]['HumanExplanation']
#         purecode = df.iloc[id]['pure code']
#         prompt = f"Given Verilog code snippet as below: \n{purecode}\n Please generate a rewritten version of it, which contains several useful assertions and each of them follows a description as follows:{humanexplanation}\n"


#         #print("1---------------------------------------------------------------")
#         completion = client.chat.completions.create(
#         model=model_name,
#         messages=[
#             {"role": "system", "content": "You are a helpful bot that generate some useful assertions for a given verilog code."},
#             {"role": "user", "content": prompt}
#         ]
#         )

#         llm_response = completion.choices[0].message.content

#         csv_writer.writerow([code,humanexplanation,purecode,prompt,llm_response])