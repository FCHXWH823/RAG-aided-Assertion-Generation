from openai import OpenAI
import pandas as pd
import csv
import random
import yaml
import json
import os
#client = OpenAI()

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

# NYU CCS's key
model_name = "o3-mini"
eval_num = 100


example_code_with_assertions = '''
module ff
  (
   input logic clk, rst, en, in,
   output logic out   
   );

   always_ff @(posedge clk or posedge rst)
      if (rst) out = 1'b0;
      else if (en) out = in;  

    assert proprty(@(posedge clk) default disable iff (rst) !en |-> out == $past(in,1));
    assert proprty(en || out == $past(in,1));
    assert property(@(posedge clk) default disable iff (rst) en |=> out == $past(in,1));
endmodule
'''

assertion_explanation_prompt = '''
step 0: extract the clock signal condition (optional), the disable condition (optional), the logical expression;
step 1: extract all signals in the logical expression; 
step 2: get all signals' explanations in the context of given verilog code;
step 3: extract all logical operators in the logical expression;
step 4: get all logical operators' explanations;
step 5: generate the explanation ONLY for the logical expression WITHOUT containing initial signal names and STRICTLY using the explanations of signals and logic operators.
'''

assertion_output_format = '''
{
"Assertion 1": {
"clock signal condition": ,
"disable condition": ,
"logical expression": ,
"Signals": [],
"Signal Explanations": {},
"Logical Operators": [],
"Logical Operators Explanation": {},
"Assertion Explaination": 
},
"Assertion 2": {
"clock signal condition": ,
"disable condition": ,
"logical expression": ,
"Signals": [],
"Signal Explanations": {},
"Logical Operators": [],
"Logical Operators Explanation": {},
"Assertion Explaination": 
},
...
}
'''

example_assertions_explanations = '''
{
"Assertion 1": {
"clock signal condition": @(posedge clk),
"disable condition": default disable iff (rst),
"logical expression": !en |-> out == $past(in,1),
"Signals": ["en", "out", "in"],
"Signal Explanations": {
          "en": "enable signal",
          "out": "output signal of the verilog module",
          "in": "input signal of the verilog module"
},
"Logical Operators": ["!", "|->", "$past", "=="],
"Logical Operators Explanation": {
          "!": "the value of a signal is reset (0)",
          "|->": "if xxxxx, xxxx",
          "$past": "the last several clock cycles",
          "==": "equal"
},
"Assertion Explaination": "if enable signal is reset (0), output signal equals the last one clock cycle's input signal"
},

"Assertion 2": {
"clock signal condition": ,
"disable condition": ,
"logical expression": en || out == $past(in,1),
"Signals": ["en", "out", "in"],
"Signal Explanations": {
          "en": "enable signal",
          "out": "output signal of the verilog module",
          "in": "input signal of the verilog module"
},
"Logical Operators": ["||", "==", "$past"],
"Logical Operators Explanation": {
          "||": "or",
          "==": "equal",
          "$past": "the last several clock cycles"
},
"Assertion Explaination": "enable signal is set (1) or output signal equals the last one clock cycle's input signal"
},

"Assertion 3": {
"clock signal condition": @(posedge clk),
"disable condition": default disable iff (rst),
"logical expression": en |=> out == $past(in,1),
"Signals": ["en", "out", "in"],
"Signal Explanations": {
          "en": "enable signal",
          "out": "output signal of the verilog module",
          "in": "input signal of the verilog module"
},
"Logical Operators": ["|=>", "==", "$past"],
"Logical Operators Explanation": {
          "|=>": "if xxxxx, xxxx since next clock cycle",
          "==": "equal",
          "$past": "the last several clock cycles"
},
"Assertion Explaination": "if enable signal is set (1), output signal equals the last one clock cycle's input signal since next clock cycle"
}
}
'''

def assertion_transform_prompt(verilog_code):
    return f'''
    Please transform the assertions in the given verilog code \n{verilog_code}\n into the following format:
    assert property (@(clock_signal_expression) disable iff(reset_signal_expression) logic_signal_expression);
    Among the format, the first two parts `@(clock_signal_expression` and `disable iff(reset_signal_expression` are optional. 

    For example, given the following example verilog code:
    module ff_sva(
    input logic clk,
    input logic rst, 
    input logic en,
    input logic in,
    input logic out
    );

        default clocking cb @(posedge clk);
        endclocking
        default disable iff (rst);

        assert proprty(!en |-> out == $past(in,1));

        assert proprty(en || out == $past(in,1));

        property p;
            @(posedge clk) disable iff (rst) en || out == $past(in,1);
        endproperty
        assert property(en |=> out == $past(in,1));

    endmodule

    the transformed assertions and output are STRICTLY as follows:
    assert proprty(@(posedge clk) disable iff (rst) !en |-> out == $past(in,1));
    assert proprty(@(posedge clk) disable iff (rst) en || out == $past(in,1));
    assert property(@(posedge clk) disable iff (rst) en |=> out == $past(in,1));
    '''

# completion = client.chat.completions.create(
#         model=model_name,
#         messages=[
#             {"role": "user", "content": "Can you give some important definition about assertions from the PDF documents?"}
#         ]
#     )
# print(completion.choices[0].message.content)

def parse_assertion_explanation(assertion_explanations):
          data = json.loads(assertion_explanations)
          explanations = {}
          for assertion_key, assertion_value in data.items():
                    explanations[assertion_key] = assertion_value["Assertion Explaination"]
          return explanations

def generate_assertions_explanation_dataset():
    for folder in os.listdir("Evaluation/Dataset"):
        folder_path = os.path.join("Evaluation/Dataset/",folder)
        if os.path.isdir(folder_path):    
            master_module = folder
            fpv_dir = "Evaluation/Dataset/"+master_module+"/"

            with open(fpv_dir+master_module+"_assertion.sv","r") as file:
                verilog_code_w_assertions = file.read()
            
            prompt = f"Given the following verilog code with several assertions: \n{verilog_code_w_assertions}\n. Please explain each of them following {assertion_explanation_prompt} and the final output must follow the format {assertion_output_format} STRICTLY and WITHOUT other contents \
            Given some assertion explanation examples: \n{example_assertions_explanations}\n"
            
            completion = client.chat.completions.create(
            model=model_name,
            messages=[
                {"role": "system", "content": "You are a helpful bot that generate explanations for some given assertions of the given verilog code."},
                {"role": "user", "content": prompt}
            ]
            )

            assertion_explanations = completion.choices[0].message.content

            with open(fpv_dir+"explanation.json","w") as file:
                file.write(assertion_explanations)



def assertion_transform():
    df = pd.read_excel('Evaluation/asserted-verilog-evaluation-dataset-new-2.xlsx')
    with open('Evaluation/asserted-verilog-evaluation-dataset-transform.csv', 'w', newline='') as csv_file:
        csv_writer = csv.writer(csv_file)
        csv_writer.writerow(['code','assertion','transformed_assertion','link'])
        for id in range(len(df)):
            code = df.iloc[id]['code']
            link = df.iloc[id]['link']
            assertion = df.iloc[id]['assertion']


            #print("1---------------------------------------------------------------")
            completion = client.chat.completions.create(
            model=model_name,
            messages=[
                {"role": "system", "content": "You are a helpful bot that transform assertions into a given format."},
                {"role": "user", "content": assertion_transform_prompt(assertion)}
            ]
            )

            transformed_assertion = completion.choices[0].message.content

            csv_writer.writerow([code,assertion,transformed_assertion,link])

# assertion_transform()

generate_assertions_explanation_dataset()

# with open('Evaluation/asserted-verilog-evaluation-dataset-new-2.csv', 'r', newline='') as csv_file:
#         df_csv = pd.read_csv('Evaluation/asserted-verilog-evaluation-dataset-new-2.csv')
#         for id in range(len(df_csv)):
#                 code = df_csv.iloc[id]['code']
#                 link = df_csv.iloc[id]['link']
#                 assertion = df_csv.iloc[id]['assertion']
#                 human_explanation = df_csv.iloc[id]['HumanExplanation']
#                 explanations = parse_assertion_explanation(human_explanation)
#                 print(explanations)


