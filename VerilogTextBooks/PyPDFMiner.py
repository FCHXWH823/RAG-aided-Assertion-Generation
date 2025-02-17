#!/usr/bin/env python3

import sys
from pdfminer.high_level import extract_pages
from pdfminer.layout import LTTextContainer, LTTextLine, LTChar

def is_monospaced_font(font_name: str) -> bool:
    """
    Return True if 'font_name' appears to be a monospaced/code font.
    Adjust these keywords for your PDFs as needed.
    """
    if not font_name:
        return False
    keywords = ["Courier", "Mono", "Consolas", "Code", "Menlo", "LucidaConsole"]
    lower_name = font_name.lower()
    return any(k.lower() in lower_name for k in keywords)

def extract_blocks(page_layout):
    """
    Parse a single page_layout (from extract_pages) and yield 'blocks' 
    as LTTextContainer objects. Each container is roughly a 'block' of text.
    """
    for element in page_layout:
        # PDFMiner lumps textual content into LTTextContainer objects
        if isinstance(element, LTTextContainer):
            yield element

def get_lines_from_block(block):
    """
    Given an LTTextContainer, extract lines plus a set of fonts used in each line.
    Return a list of dicts: [{'text': "...", 'fonts': set(...)}].
    """
    lines_info = []
    for obj in block:
        if isinstance(obj, LTTextLine):
            line_text = ""
            line_fonts = set()
            for char in obj:
                # Typically LTChar or LTAnno, LTSpace, etc.
                if isinstance(char, LTChar):
                    line_fonts.add(char.fontname)
                line_text += char.get_text()
            
            text_str = line_text.strip()
            if text_str:
                lines_info.append({
                    "text": text_str,
                    "fonts": line_fonts
                })
    return lines_info

def extract_code_snippets_from_lines(lines_info):
    """
    Group consecutive monospaced lines into multi-line "snippets".
    Return a list of snippet strings.
    """
    snippets = []
    current_snippet = []

    for line in lines_info:
        text = line["text"]
        fonts = line["fonts"]

        # We'll say a line is code if *all* fonts are monospaced (you could be more lenient)
        if fonts and all(is_monospaced_font(f) for f in fonts):
            current_snippet.append(text)
        else:
            # If we were accumulating code lines, flush them
            if current_snippet:
                snippets.append("\n".join(current_snippet))
                current_snippet = []
    
    # Flush the last snippet if present
    if current_snippet:
        snippets.append("\n".join(current_snippet))

    return snippets

def main():
    # if len(sys.argv) < 2:
    #     print("Usage: python pdfminer_extract_code.py input.pdf [page_num]")
    #     sys.exit(1)

    pdf_path = "CernyDudani-SVA- The Power of Assertions in SystemVerilog.pdf"
    page_req = 23

    # We'll process just one page for this example.
    # If you want all pages, remove the 'if i == page_req' check and accumulate results from each.
    for i, page_layout in enumerate(extract_pages(pdf_path)):
        if i == page_req:
            # 1) Extract blocks (LTTextContainer objects)
            blocks = list(extract_blocks(page_layout))

            # 2) For each block, get lines + detect fonts
            all_snippets = []
            for block in blocks:
                lines_info = get_lines_from_block(block)
                # 3) Extract consecutive code lines from these lines
                code_snips = extract_code_snippets_from_lines(lines_info)
                all_snippets.extend(code_snips)

            # 4) Print them
            print(f"Found {len(all_snippets)} code snippet(s) on page {page_req}.\n")
            for idx, snippet in enumerate(all_snippets, start=1):
                print(f"--- Code Snippet #{idx} ---")
                print(snippet)
                print("--------------------------\n")
            
            break  # stop after the requested page

if __name__ == "__main__":
    main()
