import csv
import re

# Use a set to store unique PDF names
pdf_names = set()

# Open your CSV file (adjust the filename/path as needed)
with open('/Users/fch/Python/RAG-aided-Assertion-Generation/VerilogTextBooks/fulltextbook-gptresponse.csv', newline='', encoding='utf-8') as csvfile:
    reader = csv.reader(csvfile)
    for row in reader:
        # Assuming the file path is in the first column
        path = row[0]
        # Use a regex to capture the PDF name:
        match = re.search(r'/([^/]+)_p\d+\.jpg$', path)
        if match:
            pdf_name = match.group(1)
            pdf_names.add(pdf_name)

# Convert the set to a list if needed
unique_pdf_names = list(pdf_names)

with open("/Users/fch/Python/RAG-aided-Assertion-Generation/VerilogTextBooks/AllTextBooks.txt","w") as TxtFile:
    for pdf in unique_pdf_names:
        TxtFile.write(f"{pdf}\n")

print(unique_pdf_names)
