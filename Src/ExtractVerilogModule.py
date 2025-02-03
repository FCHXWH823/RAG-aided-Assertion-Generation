import re
import yaml
import sys,os

def extract_and_write_verilog_modules(text, llm, dir):
    # Find the position of the start marker for Verilog code
    start_idx = text.find("```verilog")
    if start_idx == -1:
        print("No Verilog code block found.")
        return

    # Adjust the text to start from the found index
    text = text[start_idx:]
    # Define a regular expression pattern to capture any Verilog module
    pattern = re.compile(
        r"module\s+(\w+).*?;"  # Match the module declaration and capture the module name
        r"(.*?)"               # Non-greedy match of the module body
        r"endmodule",          # Match the end of the module
        re.DOTALL              # DOTALL to match across multiple lines including newline
    )
    
    # Find all matches in the text
    matches = pattern.findall(text)
    if not matches:
        print("No modules found.")
        return

    # check the existence of dir
    if not os.path.exists(dir):
          os.makedirs(dir)
    # Process each found module
    for name, body in matches:
        # Format the module content
        module_content = f"module {name};{body}endmodule"
        
        # Write the module to a file with the module name as the filename
        if llm:
             file_name = f"{name}_llm.sv"
        else:
             file_name = f"{name}_RAG_llm.sv"
        with open(f"{dir}/{file_name}", 'w') as file:
            file.write(module_content)
        print(f"Module {name} written to {file_name}.")

