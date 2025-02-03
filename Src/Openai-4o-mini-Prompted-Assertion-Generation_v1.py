from openai import OpenAI
import pandas as pd
import csv
import random
import yaml
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
model_name = "gpt-4o-mini-2024-07-18"

purecode = '''
module mux_func
(
  // global signals
  input  logic [127:0] a,
  input  logic [127:0] b,
  output logic [127:0] c,
  input  logic [127:0] d,
  input  logic clk,
  input  logic rst
);

logic rdy_out_sha, rdy_out_md5;
logic [127:0] aes_out;
logic [127:0] sha_out;
logic [127:0] md5_out;
logic [127:0] temperature_out;

  aes_1cc aes(
  .clk(0),
  .rst(1),
  .g_input(b),
  .e_input(a),
  .o(aes_out)
  );

  keccak sha(
  .clk(clk),
  .reset(rst),
  .in(a),
  .in_ready(1),
  .out(sha_out),
  .out_ready(rdy_out)
  );

  md5 md5(
  .clk(clk),
  .reset(rst),
  .data_i(a[31:0]),
  .load_i(1),
  .ready_o(rdy_out_md5),
  .data_o(md5_out[31:0])
  );

  tempsen temperature_sensor(
  .clk(clk),
  .in(a),
  .out(temperature_out)
  );

  always @(posedge clk) begin
    if(d[0] == 1'b1) c = aes_out;
    if(d[1] == 1'b1) c = sha_out;
    if(d[2] == 1'b1) c = md5_out;
    if(d[3] == 1'b1) c = temperature_out;
    else c = 128'h0000_0000_0000_0000_0000_0000_0000_0000;
  end
  
  
  //assign c = (a & ~b) | (~a & b);  

endmodule // cust_xor
'''

humanexplanation = '''
This assertion aims at finding the bug that Output of MAC is not erased on reset.
'''

prompt = f"Given Verilog code snippet as below: \n{purecode}\n Please generate a verilog assertion for it, following the description as follows:{humanexplanation}\n"


#print("1---------------------------------------------------------------")
completion = client.chat.completions.create(
model=model_name,
messages=[
    {"role": "system", "content": "You are a helpful bot that generate some useful assertions for a given verilog code."},
    {"role": "user", "content": prompt}
]
)

llm_response = completion.choices[0].message.content

print(llm_response)