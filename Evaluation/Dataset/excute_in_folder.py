import os 
import sys

def excute_in_each_folder(folder = "", a=1, b=1, c=1):
    folder_path = os.path.join("./",folder)
    # print(f"a:{a}, b:{b}, c:{c}")
    if os.path.isdir(folder_path):
        if a:
            os.system(f"cd {folder_path}; jg -no_gui fpv_Openai-4o-mini.tcl")
            print("============================finished fpv_Openai-4o-mini.tcl==================================")
        if b:
            os.system(f"cd {folder_path}; jg -no_gui fpv_RAG_Openai-4o-mini.tcl")
            print("============================finished fpv_RAG_Openai-4o-mini.tcl==================================")
        if c:
            os.system(f"cd {folder_path}; jg -no_gui fpv_Dynamic_RAG_Openai-4o-mini.tcl")
            print("============================finished fpv_Dynamic_RAG_Openai-4o-mini.tcl==================================")
        os.system(f"cd {folder_path}; rm -r jgproject")

def excute_in_folders_1():
    for folder in os.listdir("./"):
        folder_path = os.path.join("./",folder)
        if os.path.isdir(folder_path):
            os.system(f"rm -r jgproject; cd {folder_path}; jg -no_gui fpv_Openai-4o-mini.tcl > jg_intermidiate_Openai-4o-mini.rpt; rm -r jgproject; cd ..;")
            print(f"============================={folder}-Openai-4o-mini finished")

def excute_in_folders_2():
    for folder in os.listdir("./"):
        folder_path = os.path.join("./",folder)
        if os.path.isdir(folder_path):
            os.system(f"cd {folder_path}; jg -no_gui fpv_RAG_Openai-4o-mini.tcl > jg_intermidiate_RAG-Openai-4o-mini.rpt; rm -r jgproject; cd ..;")

def excute_in_folders_3():
    for folder in os.listdir("./"):
        folder_path = os.path.join("./",folder)
        if os.path.isdir(folder_path):
            os.system(f"cd {folder_path}; jg -no_gui fpv_Dynamic_RAG_Openai-4o-mini.tcl > jg_intermidiate_Dynamic_RAG-Openai-4o-mini.rpt; rm -r jgproject; cd ..;")


# excute_in_folders_1()
# excute_in_folders_2()
# print(f"argv[2]:{sys.argv[2]}, argv[3]:{sys.argv[3]}, argv[4]:{sys.argv[4]}")
if len(sys.argv) == 5:
    a = int(sys.argv[2])
    b = int(sys.argv[3])
    c = int(sys.argv[4])
else:
    a = 1
    b = 1
    c = 1
excute_in_each_folder(sys.argv[1], a, b, c)