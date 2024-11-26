from openai import OpenAI
import pandas as pd
import csv
import random
#client = OpenAI()

def init_prompt_template_completion(model_id,code):
    return client.chat.completions.create(
        model=model_id,
        messages=[
            {"role": "system", "content": "You are a helpful bot that provides a brief explanation of the input code."},
            {"role": "user", "content": "Given input code snippet as below: \n" + code + "\n Please give a brief explanation of the code. \n"}
        ]
    )

client = OpenAI(
        api_key=""
)

#model_name = "ft:gpt-3.5-turbo-0125:personal::A9KbE7Vx"
# initial key
# model_name_1 = "ft:gpt-4o-mini-2024-07-18:personal::ADG5sJhx" # initial prompt template ,epoch: 1
# model_name_2 = "ft:gpt-4o-mini-2024-07-18:personal::ADOVxQ34" # initial prompt template, epoch: 2
# model_name_3 = "ft:gpt-4o-mini-2024-07-18:personal::ADRj5YX0" # new prompt template, epoch: 1
# model_name_4 = "ft:gpt-4o-mini-2024-07-18:personal::ADYuwFrD" # initial prompt template, epoch: 10
# model_name_5 = "ft:gpt-4o-mini-2024-07-18:personal::ADefsoKl" # new prompt template, epoch: 10

# NYU CCS's key
model_name = "gpt-4o-mini-2024-07-18"
eval_num = 100


df = pd.read_csv('asserted-verilog-evaluation-dataset.csv')

# completion = client.chat.completions.create(
#         model=model_name,
#         messages=[
#             {"role": "user", "content": "Can you give some important definition about assertions from the PDF documents?"}
#         ]
#     )
# print(completion.choices[0].message.content)

with open('eval-results.csv', 'w', newline='') as csv_file:
    csv_writer = csv.writer(csv_file)
    csv_writer.writerow(['code','HumanExplanation','pure code','prompt','llm_response'])
    for id in range(len(df)):
        code = df.iloc[id]['code']
        humanexplanation = df.iloc[id]['HumanExplanation']
        purecode = df.iloc[id]['pure code']
        prompt = "Given Verilog code snippet as below: \n" + purecode + "\n Please generate a rewritten version of it, which contains some useful assertions for verification. \n"


        #print("1---------------------------------------------------------------")
        completion = client.chat.completions.create(
        model=model_name,
        messages=[
            {"role": "system", "content": "You are a helpful bot that generate some useful assertions for a given verilog code."},
            {"role": "user", "content": prompt}
        ]
        )

        llm_response = completion.choices[0].message.content

        csv_writer.writerow([code,humanexplanation,purecode,prompt,llm_response])