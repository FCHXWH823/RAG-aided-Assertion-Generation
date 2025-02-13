import os 

def excute_in_folders_1():
    for folder in os.listdir("./"):
        folder_path = os.path.join("./",folder)
        if os.path.isdir(folder_path):
            os.system(f"cd {folder_path}; jg -no_gui fpv_Openai-4o-mini.tcl; rm -r jgproject; cd ..;")

def excute_in_folders_2():
    for folder in os.listdir("./"):
        folder_path = os.path.join("./",folder)
        if os.path.isdir(folder_path):
            os.system(f"cd {folder_path}; jg -no_gui fpv_RAG_Openai-4o-mini.tcl; rm -r jgproject; cd ..;")



excute_in_folders_1()
excute_in_folders_2()