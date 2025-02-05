import os
import shutil
import pandas as pd


def get_all_maintained_folders():
    df = pd.read_csv("Evaluation/asserted-verilog-evaluation-dataset-transform.csv")
    folders_list = []
    for i in range(len(df)):
        folders_list.append(df.iloc[i]['Master Module'])
    
    return folders_list

def remove_unlisted_folders(current_dir, keep_list):
    
    for item in os.listdir(current_dir):
        item_path = os.path.join(current_dir, item)
        if os.path.isdir(item_path) and item not in keep_list:
            print(f"Removing folder: {item_path}")
            shutil.rmtree(item_path)


print(get_all_maintained_folders())
remove_unlisted_folders("Evaluation/Dataset",get_all_maintained_folders())

print(os.listdir("Evaluation/Dataset"))
print(len(os.listdir("Evaluation/Dataset")))