import pandas as pd
import csv
from ExtractVerilogModule import *
if __name__ == '__main__':
    import yaml

    with open("Src/Config.yml") as file:
        config = yaml.safe_load(file)
    PDF_Name = config["PDF_Name"]
    df_llm_response = pd.read_csv("Results/Openai-4o-mini-Prompted-Assertion-Generation-Results.csv")
    df_rag_llm_response = pd.read_csv(f"Results/RAG-Openai-4o-mini-Prompted-Assertion-Generation-Results-{PDF_Name}.csv")

    with open(f"Results/Prompted-Assertion-Generation-Results-{PDF_Name}.csv","w") as file:
        csv_writer = csv.writer(file)
        csv_writer.writerow(['HumanExplanation','pure code','prompt','code','llm_response','llm_rag_response'])
        for i in range(len(df_llm_response)):
            humanexplanation = df_llm_response.iloc[i]['HumanExplanation']
            purecode = df_llm_response.iloc[i]['pure code']
            prompt = df_llm_response.iloc[i]['prompt']
            code = df_llm_response.iloc[i]['code']
            llm_response = df_llm_response.iloc[i]['llm_response']
            llm_rag_response = df_rag_llm_response.iloc[i]['llm_response']
            csv_writer.writerow([humanexplanation,purecode,prompt,code,llm_response,llm_rag_response])

            extract_and_write_verilog_modules(llm_response,True,f"Results/Verilog/{PDF_Name}")
            extract_and_write_verilog_modules(llm_rag_response,False,f"Results/Verilog/{PDF_Name}")
    