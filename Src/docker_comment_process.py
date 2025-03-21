import docker
import os
import tarfile
import io
import sys



def upload_file_to_container(container, local_file_dir, local_file, container_file_dir):
    tar_stream = io.BytesIO()
    with tarfile.open(fileobj=tar_stream, mode="w") as tar:
        tar.add(local_file_dir+local_file, arcname=local_file)
    tar_stream.seek(0)
    container.put_archive(container_file_dir, tar_stream.getvalue())

def execute_command_in_container(container, command):
    exit_code, output = container.exec_run(command)
    print(f"Command output: {output.decode('utf-8')}")
    return exit_code

def download_file_from_container(container, output_container_file_dir, output_container_file, output_local_file_dir):
    bits, stat = container.get_archive(output_container_file_dir+output_container_file)
    tar_bytes = io.BytesIO(b"".join(bits))
    with tarfile.open(fileobj=tar_bytes, mode="r") as tar:
        tar.extractall(path=output_local_file_dir)

client = docker.from_env()
container = client.containers.run(
    image='phyzli/ubuntu18.04_xfce4_vnc4server_synopsys',
    hostname='lizhen',
    mac_address='02:42:ac:11:00:02',
    detach=True,
    tty=True,
    stdin_open=True
)

for folder in os.listdir("Evaluation/Dataset/"):
    folder_path = os.path.join("Evaluation/Dataset/",folder)
    if os.path.isdir(folder_path):
        print(f"===================== Processing folder: {folder} ====================")
        

        design = folder
        if design != "or1200_ctrl":
            continue
        leaf_design = "or1200_defines.v"
        local_file_dir = f"Evaluation/Dataset/{design}/"

        llm = "deepseek-chat"

        container_file_dir = '/testSV/'

        # try:
        execute_command_in_container(container,"mkdir testSV")

        upload_file_to_container(container, "Src/", "extraction.py", container_file_dir)
        upload_file_to_container(container, local_file_dir, leaf_design, container_file_dir)
        upload_file_to_container(container, local_file_dir, leaf_design, '/')
        upload_file_to_container(container, local_file_dir, f"{design}_{llm}.sv", container_file_dir)
        upload_file_to_container(container, local_file_dir, f"{design}_nl2spec-{llm}.sv", container_file_dir)
        upload_file_to_container(container, local_file_dir, f"{design}_RAG-{llm}.sv", container_file_dir)
        upload_file_to_container(container, local_file_dir, f"{design}_Dynamic-RAG-{llm}.sv", container_file_dir)

        # execute_command_in_container(container,"cd testSV")
        execute_command_in_container(container,"python3 /testSV/extraction.py /testSV/{leaf_design} /testSV/{design}_{llm}.sv".format(leaf_design=leaf_design,design=design,llm=llm))
        execute_command_in_container(container,"python3 /testSV/extraction.py /testSV/{leaf_design} /testSV/{design}_nl2spec-{llm}.sv".format(leaf_design=leaf_design,design=design,llm=llm))
        execute_command_in_container(container,"python3 /testSV/extraction.py /testSV/{leaf_design} /testSV/{design}_RAG-{llm}.sv".format(leaf_design=leaf_design,design=design,llm=llm))
        execute_command_in_container(container,"python3 /testSV/extraction.py /testSV/{leaf_design} /testSV/{design}_Dynamic-RAG-{llm}.sv".format(leaf_design=leaf_design,design=design,llm=llm))

        download_file_from_container(container,"/testSV/", f"{design}_{llm}.sv", local_file_dir+"testSV/")
        download_file_from_container(container,"/testSV/", f"{design}_nl2spec-{llm}.sv", local_file_dir+"testSV/")
        download_file_from_container(container,"/testSV/", f"{design}_RAG-{llm}.sv", local_file_dir+"testSV/")
        download_file_from_container(container,"/testSV/", f"{design}_Dynamic-RAG-{llm}.sv", local_file_dir+"testSV/")

        print(f"===================== Finished processing folder: {folder} ====================")

        # finally:
        #     container.stop()
        #     container.remove()
