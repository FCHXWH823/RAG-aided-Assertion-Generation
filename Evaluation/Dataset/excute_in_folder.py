import os 

def excute_in_folders():
    for folder in os.listdir("./"):
        folder_path = os.path.join("./",folder)
        if os.path.isdir(folder_path):
            os.system(f"cd {folder_path}; jg -no_gui fpv.tcl; cd ..;")


excute_in_folders()