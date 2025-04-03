import re
import sys
import os

def parse_vcs_errors(vcs_output_lines):
    """
    Parses VCS output lines to extract errors of the form:
    
    1) Error-[SE] Syntax error
       "counter.sv", 29: token is '('
       ...
       
    2) Error-[IND] Identifier not declared
       counter.sv, 356
       ...
    
    Returns a list of dictionaries, each containing:
      {
        'error_type': <string, e.g. 'SE'>,
        'error_message': <string, e.g. 'Syntax error'>,
        'file': <string, e.g. 'counter.sv'>,
        'line': <int, e.g. 29>
      }
    """
    # Regex to capture lines like:
    # Error-[SE] Syntax error
    # Error-[IND] Identifier not declared
    error_type_regex = re.compile(r'^Error-\[(?P<code>[^\]]+)\]\s+(?P<message>.*)')
    
    # This regex should match both:
    #  - "counter.sv", 29: token is '('
    #  - counter.sv, 356
    # Explanation:
    #   ^"?(?P<file>[^"]+)"?  -> optional quotes around the filename
    #   ,\s*(?P<line>\d+)    -> comma, optional space, then a number
    #   (?::.*)?$            -> optional colon plus anything else
    file_line_regex = re.compile(r'^"?(?P<file>[^"]+)"?,\s*(?P<line>\d+)(?::.*)?$')

    errors_found = []
    current_error = None

    for line in vcs_output_lines:
        line = line.strip()

        # 1. Check if this line starts a new error block
        match_err = error_type_regex.match(line)
        if match_err:
            # If we had a previous error that didn't get a file/line, we can store it as-is
            if current_error:
                errors_found.append(current_error)
            
            current_error = {
                'error_type': match_err.group('code'),       # e.g. 'SE', 'IND'
                'error_message': match_err.group('message'), # e.g. 'Syntax error', 'Identifier not declared'
                'file': None,
                'line': None
            }
            continue

        # 2. Check if this line contains file and line number
        match_file = file_line_regex.match(line)
        if match_file and current_error:
            current_error['file'] = match_file.group('file')
            current_error['line'] = int(match_file.group('line'))
            
            # We assume the file/line we just parsed belongs to the "current_error".
            # After attaching file/line, we can finalize this error record.
            errors_found.append(current_error)
            current_error = None
            continue

    # In case the log ends with an error message but no file/line was found
    if current_error:
        errors_found.append(current_error)
    # print(errors_found) 
    return errors_found

def comment_out_verilog_lines(errors, verilog_file):
    """
    Comments out the lines in `verilog_file` that are reported as errors in `errors`.
    
    :param errors: List of error dicts from parse_vcs_errors().
    :param verilog_file: The Verilog file to modify.
    """
    # Gather all line numbers in this file that have errors
    lines_with_errors = set(
        err['line'] for err in errors 
        if err['file'] == verilog_file and err['line'] is not None
    )
    
    if not lines_with_errors:
        print(f"[Info] No errors found for file: {verilog_file}")
        return
    
    if not os.path.isfile(verilog_file):
        print(f"[Warning] File not found: {verilog_file}")
        return
    
    # Read the Verilog file
    try:
        with open(verilog_file, 'r') as f:
            file_lines = f.readlines()
    except Exception as e:
        print(f"[Error] Could not read {verilog_file}: {e}")
        return
    
    # Comment out lines that have errors (VCS is 1-based, Python lists are 0-based)
    for i in range(len(file_lines)):
        if (i + 1) in lines_with_errors:
            stripped_line = file_lines[i].lstrip()
            if not stripped_line.startswith('//'):
                file_lines[i] = '// ' + file_lines[i]
    # print(file_lines)    
    # Write the updated file
    try:
        with open(verilog_file, 'w') as f:
            f.writelines(file_lines)
        print(f"[Info] Commented out lines {sorted(lines_with_errors)} in {verilog_file}")
    except Exception as e:
        print(f"[Error] Could not write to {verilog_file}: {e}")


def main():
    path = sys.argv[1]
    with open(path) as file:
        sample_vcs_output = file.readlines()
    # Example VCS output lines
    # sample_vcs_output = [
    #    "Error-[SE] Syntax error",
    #    "  Following verilog source has syntax error :",
    #    "  \"counter.sv\", 29: token is '('",
    #    "  assert property (@(posedge clk)  (eventually (rst == 1 || digit_select == 1)));",
    #    "",
    #    "Error-[IND] Identifier not declared",
    #    "counter.sv, 356",
    #    "  Identifier 'st_wenablep' has not been declared yet. If this error is not expected...",
    #    "",
    #    "Some other text..."
    #]

    # Parse the sample output
    errors = parse_vcs_errors(sample_vcs_output)

    # Print results
    for err in errors:
        print(f"Error Type: {err['error_type']}")
        print(f"Message:    {err['error_message']}")
        print(f"File:       {err['file']}")
        print(f"Line:       {err['line']}")
        print("----------")

    comment_out_verilog_lines(errors, "counter.sv")

if __name__ == '__main__':
    if len(sys.argv) != 3:
        sv_path = sys.argv[1]
    else:
        sv_path = sys.argv[1]+" "+sys.argv[2]
    os.system(f"vcs -parse_only -assert svaext -sverilog {sv_path} +error+100 > vcs.rpt")
    while 1:
        with open("vcs.rpt") as file:
            sample_vcs_output = file.readlines()

        # Parse the sample output
        errors = parse_vcs_errors(sample_vcs_output)

        if not errors:
            break

        # Print results
        print("===============================================")
        for err in errors:
            print(f"Error Type: {err['error_type']}")
            print(f"Message:    {err['error_message']}")
            print(f"File:       {err['file']}")
            print(f"Line:       {err['line']}")
            print("----------\n")

        comment_out_verilog_lines(errors, sv_path)

        os.system(f"vcs -parse_only -assert svaext -sverilog {sv_path} +error+100 > vcs.rpt")


