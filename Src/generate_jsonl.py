import csv
import json

# Define the constant system message
# system_message = "You are a helpful bot that provides a brief explanation of the input code."
system_message = "You are a helpful bot that generate some useful assertions for a given verilog code."

# Open the CSV file (replace 'input.csv' with your CSV file name)
with open('asserted-verilog-evaluation-dataset.csv', 'r', newline='', encoding='utf-8') as csvfile, open('asserted-verilog-evaluation-dataset.jsonl', 'w', encoding='utf-8') as jsonlfile:
    reader = csv.reader(csvfile)

    # Process each row in the CSV
    for i, row in enumerate(reader, start=1):
        # Check if the row has at least 3 fields
        if len(row) >= 3:
            # Extract the necessary fields
            # user_content = "Given input code snippet as below: \n" + row[3] + "\n Please give a brief explanation of the code. \n"
            user_content = "Given Verilog code snippet as below: \n" + row[2] + "\n Please generate a rewritten version of it, which contains some useful assertions for verification. \n"
            assistant_content = row[3]

            # Construct the JSON object for this entry
            entry = {
                "messages": [
                    {"role": "system", "content": system_message},
                    {"role": "user", "content": user_content},
                    {"role": "assistant", "content": assistant_content}
                ]
            }

            # Write the JSON object to the JSONL file
            jsonlfile.write(json.dumps(entry, ensure_ascii=False) + '\n')
        else:
            print(f'Row {i} skipped: Not enough fields.')

print('Created all_entries.jsonl.')

