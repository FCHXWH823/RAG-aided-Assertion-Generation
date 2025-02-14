#Author Derek Ekberg

# Standard library imports
import re
import sys
from pathlib import Path
from typing import List, Optional

# Third-party imports
from PyPDF2 import PdfReader

# Local imports
from verilog_patterns import VERILOG_PATTERNS, split_mixed_content, is_likely_prose
import yaml
from text_code_processor import *


class PDFTextProcessor:
    def __init__(self):
        # Patterns for basic structure detection
        self.chapter_pattern = re.compile(r'^Chapter\s+\d+:.*$', re.MULTILINE)
        self.section_pattern = re.compile(r'^\d+\.\d+.*$', re.MULTILINE)

        # Expanded code start indicators
        self.code_start_indicators = [
            # Basic Verilog constructs
            'module', 'always', 'initial', 'assign', 'wire', 'reg',
            # SystemVerilog constructs
            'interface', 'package', 'program', 'class', 'struct',
            'typedef', 'enum', 'assert', 'assume', 'cover',
            # Common starting keywords
            'logic', 'parameter', 'localparam'
        ]

        # Code end indicators
        self.code_end_indicators = [
            'endmodule', 'endinterface', 'endpackage', 'endprogram',
            'endclass', 'endgenerate', ');'
        ]

        self.min_code_chars = 10  # Minimum characters to consider as code block

    def process_line(self, line: str) -> List[str]:
        """Process a single line that might contain mixed content."""
        segments = split_mixed_content(line)
        processed_lines = []

        current_text = ""
        for text, is_code in segments:
            if is_code and len(text.strip()) >= self.min_code_chars:
                if current_text.strip():
                    processed_lines.append(current_text)
                    current_text = ""
                processed_lines.append("```verilog")
                processed_lines.append(text)
                processed_lines.append("```")
            else:
                current_text += text

        if current_text.strip():
            processed_lines.append(current_text)

        return processed_lines

    def extract_text_from_pdf(self, pdf_path: str) -> Optional[str]:
        """Extract text from PDF while preserving original formatting and handling inline code."""
        try:
            reader = PdfReader(pdf_path)
            processed_pages = []

            for page in reader.pages:
                text = page.extract_text()
                if not text:
                    continue

                processed_lines = []
                in_code_block = False
                code_indent_level = 0

                for line in text.split('\n'):
                    # Skip empty lines and page numbers
                    if not line.strip() or re.match(r'^\s*\d+\s*$', line):
                        continue

                    stripped_line = line.strip()
                    current_indent = len(line) - len(stripped_line)

                    # Check for code block start/end
                    if not in_code_block:
                        if any(re.search(pattern, stripped_line) for pattern in VERILOG_PATTERNS):
                            if not is_likely_prose(stripped_line):
                                processed_lines.append("```verilog")
                                in_code_block = True
                                code_indent_level = current_indent
                    else:
                        if (current_indent < code_indent_level and not any(
                                re.search(pattern, stripped_line) for pattern in VERILOG_PATTERNS)) or \
                                any(indicator in stripped_line for indicator in self.code_end_indicators):
                            processed_lines.append(line)
                            processed_lines.append("```")
                            in_code_block = False
                            continue

                    if in_code_block:
                        processed_lines.append(line)
                    else:
                        # Process line for inline code
                        line_segments = self.process_line(line)
                        processed_lines.extend(line_segments)

                # Close any open code block
                if in_code_block:
                    processed_lines.append("```")

                processed_pages.extend(processed_lines)

            full_text = '\n'.join(processed_pages)

            # Handle hyphenated word splits
            full_text = re.sub(r'(\w+)-\s*\n\s*(\w+)', r'\1\2', full_text)

            return full_text

        except Exception as e:
            print(f"Error processing PDF: {str(e)}")
            return None

    def process_pdf_to_file(self, input_pdf: str, output_txt: str) -> bool:
        """Process PDF and save to text file."""
        try:
            processed_text = self.extract_text_from_pdf(input_pdf)
            if processed_text:
                output_path = Path(output_txt)
                output_path.write_text(processed_text, encoding='utf-8')
                print(f"Processed text saved to: {output_txt}")
                return True
            return False

        except Exception as e:
            print(f"Error saving processed text: {str(e)}")
            return False
        
if __name__ == "__main__":
    with open("Src/Config.yml") as file:
        config = yaml.safe_load(file)
    
    PDF_Name = config["PDF_Name"]

    """Process PDF and optionally query the processed content."""
    PDF_Processor = PDFTextProcessor()
    pdf_text = PDF_Processor.extract_text_from_pdf(f"VerilogTextBooks/{PDF_Name}.pdf")
    processor = VerilogTextbookProcessor()
    print(len(pdf_text))
    processor.process_document(pdf_text)
    results = processor.query("How to implement a D flip-flop?")
    print(len(results))
    for chunk in results:
        print(f"Type: {chunk.chunk_type}")
        print(f"Content: {chunk.content}")
        print("---")