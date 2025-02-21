import re
import os
import sys
import json
import csv

def extract_rpt_data(dir_path,rpt_file="fpv_Openai-4o-mini.rpt"):
    filepath = os.path.join(dir_path,rpt_file)
    # Updated pattern to account for potential spaces and exact line structure from the file
    pattern = re.compile(r'\[\d+\]\s+(\S+._assert_\d+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)')
    results = []

    with open(filepath, 'r') as file:
        for line in file:
            match = pattern.match(line.strip())
            if match:
                results.append(match.groups())

    return results

def get_num_golden_assertions(dir_path):
    filepath = os.path.join(dir_path,"explanation.json")
    with open(filepath,"r") as file:
          assertions = json.load(file)
    return len(assertions)

def get_num_sc_fc_fm(results, num_golden_assertions):
    num_sc = int((len(results) - num_golden_assertions) / 2)
    num_fc = 0
    num_fm = 0
    for i in range(num_sc):
          id_fc = num_golden_assertions + 2*i
          num_fc += 1 if 'proven' in results[id_fc][1] else 0
          id_fm = num_golden_assertions + 2*i + 1
          num_fm += 1 if 'proven' in results[id_fm][1] else 0
    return num_sc, num_fc, num_fm




with open("../Results/Prompted-Assertion-Generation-Results-over-New-Evaluation-Dataset.csv","w") as file:
    csv_writer = csv.writer(file)
    for folder in os.listdir("../Evaluation/Dataset"):
        folder_path = os.path.join("../Evaluation/Dataset/",folder)
        if os.path.isdir(folder_path):
            extract_data_openai_4o = extract_rpt_data(folder_path,"fpv_Openai-4o-mini.rpt")
            sc_openai_4o, fc_openai_4o, fm_openai_4o = get_num_sc_fc_fm(extract_data_openai_4o,get_num_golden_assertions(folder_path))    
            extract_data_rag_openai_4o = extract_rpt_data(folder_path,"fpv_RAG-Openai-4o-mini.rpt")    
            sc_rag_openai_4o, fc_rag_openai_4o, fm_rag_openai_4o = get_num_sc_fc_fm(extract_data_rag_openai_4o,get_num_golden_assertions(folder_path))    
            extract_data_dynamic_rag_openai_4o = extract_rpt_data(folder_path,"fpv_Dynamic-RAG-Openai-4o-mini.rpt")    
            sc_dynamic_rag_openai_4o, fc_dynamic_rag_openai_4o, fm_dynamic_rag_openai_4o = get_num_sc_fc_fm(extract_data_dynamic_rag_openai_4o,get_num_golden_assertions(folder_path))    