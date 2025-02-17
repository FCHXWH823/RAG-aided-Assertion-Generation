#!/usr/bin/env python3

import fitz  # PyMuPDF

# --------------------------------------------------------------------
# Part 1: Utility to detect whether a font is likely "code" (monospaced)
# --------------------------------------------------------------------
def is_code_font(font_name):
    """
    Returns True if the font name suggests a monospaced / code font.
    Customize this for your specific PDF(s).
    """
    if not font_name:
        return False
    
    # Common monospaced font indicators:
    monospaced_keywords = [
        "Courier", "Mono", "Consolas", "Code", "Menlo", "LucidaConsole", "RobotoMono"
    ]
    font_lower = font_name.lower()
    return any(keyword.lower() in font_lower for keyword in monospaced_keywords)


# --------------------------------------------------------------------
# Part 2: Heuristics to merge blocks from MuPDF
# --------------------------------------------------------------------
def blocks_are_close(block_a, block_b, y_threshold=10, x_overlap_ratio=0.3):
    """
    Determine if two blocks are 'close enough' to be merged.
    block["bbox"] = [x0, y0, x1, y1]
    
    - y_threshold: max vertical gap to consider them adjacent.
    - x_overlap_ratio: fraction of horizontal overlap needed.
    """
    x0a, y0a, x1a, y1a = block_a["bbox"]
    x0b, y0b, x1b, y1b = block_b["bbox"]

    # Assume block_b is below block_a in reading order:
    vertical_gap = y0b - y1a  # difference between top of b and bottom of a
    if vertical_gap > y_threshold:
        return False
    
    # Check horizontal overlap
    overlap_left = max(x0a, x0b)
    overlap_right = min(x1a, x1b)
    overlap_width = max(0, overlap_right - overlap_left)

    width_a = x1a - x0a
    width_b = x1b - x0b
    min_width = min(width_a, width_b)
    if min_width == 0:
        return False

    actual_overlap_ratio = overlap_width / min_width
    return actual_overlap_ratio >= x_overlap_ratio


def merge_two_blocks(block_a, block_b):
    """
    Merge block_b into block_a, updating text lines and bounding box.
    """
    block_a["lines"].extend(block_b["lines"])
    x0a, y0a, x1a, y1a = block_a["bbox"]
    x0b, y0b, x1b, y1b = block_b["bbox"]
    # Expand block_a bbox to encompass both
    block_a["bbox"] = [
        min(x0a, x0b), min(y0a, y0b),
        max(x1a, x1b), max(y1a, y1b)
    ]
    return block_a


def get_merged_blocks(page, y_threshold=10, x_overlap_ratio=0.3):
    """
    1) Extract text blocks from page.
    2) Sort them top-to-bottom, left-to-right.
    3) Merge 'close' blocks per our heuristic.
    4) Return a list of merged blocks.
    """
    page_dict = page.get_text("dict")
    raw_blocks = page_dict.get("blocks", [])

    # Filter to text blocks only
    text_blocks = [b for b in raw_blocks if "lines" in b and b["lines"]]

    # Sort blocks by top-left
    text_blocks.sort(key=lambda b: (b["bbox"][1], b["bbox"][0]))

    merged_blocks = []
    current_block = None

    for block in text_blocks:
        if current_block is None:
            current_block = block
        else:
            if blocks_are_close(current_block, block,
                                y_threshold=y_threshold,
                                x_overlap_ratio=x_overlap_ratio):
                # Merge into current block
                current_block = merge_two_blocks(current_block, block)
            else:
                # Finalize the current block and start a new one
                merged_blocks.append(current_block)
                current_block = block

    # Flush the last one
    if current_block:
        merged_blocks.append(current_block)

    return merged_blocks


# --------------------------------------------------------------------
# Part 3: Extract code snippets from the (merged) blocks
#         We'll do a line-based approach: a line is "code" only if
#         *all spans* in that line are monospaced.
# --------------------------------------------------------------------
def extract_code_snippets_from_block(block):
    """
    Returns a list of code snippets found within a single block.
    We treat consecutive "code lines" as one snippet.
    """
    snippet_list = []
    current_snippet_lines = []

    for line in block.get("lines", []):
        spans = line.get("spans", [])
        # Check if entire line is code
        line_is_code = True
        fragments = []
        
        for span in spans:
            text_piece = span.get("text", "")
            font_name = span.get("font", "")
            if not is_code_font(font_name):
                line_is_code = False
            fragments.append(text_piece)
        
        line_text = "".join(fragments).strip()

        if line_is_code and line_text:
            # Accumulate line in snippet
            current_snippet_lines.append(line_text)
        else:
            # flush if we had code lines in progress
            if current_snippet_lines:
                snippet_list.append("\n".join(current_snippet_lines))
                current_snippet_lines = []
    
    # end of block: if we still have code lines, flush them
    if current_snippet_lines:
        snippet_list.append("\n".join(current_snippet_lines))

    return snippet_list


def block_to_text(block):
    """
    Given one merged block dict with a 'lines' key, convert
    it into a multi-line text string.
    """
    text_lines = []
    for line in block.get("lines", []):
        # Gather all spans in that line
        spans = line.get("spans", [])
        # Join their text
        line_text = "".join(span.get("text", "") for span in spans)
        text_lines.append(line_text)
    
    # Join all lines with newline separators
    return "\n".join(text_lines)

# --------------------------------------------------------------------
# Part 4: Main script demonstration
# --------------------------------------------------------------------
def main():
    
    pdf_path = "CernyDudani-SVA- The Power of Assertions in SystemVerilog.pdf"
    page_num = 23

    doc = fitz.open(pdf_path)
    
    page = doc[page_num]
    print(page.get_text())
    page_dict = page.get_text("dict")
    raw_blocks = page_dict.get("blocks", [])

    for raw_block in raw_blocks:
        print(block_to_text(raw_block))
        x0,y0,x1,y1 = raw_block["bbox"]
        print(f"--------------x0:{x0}, x1:{x1}--------------\n\n")
        print("\n")

    # 1) Merge blocks
    merged_blocks = get_merged_blocks(page, y_threshold=10, x_overlap_ratio=0.3)

    for block in merged_blocks:
        print(block_to_text(block))
        

    # 2) For each merged block, extract code snippets
    all_code_snippets = []
    for mblock in merged_blocks:
        code_snippets = extract_code_snippets_from_block(mblock)
        all_code_snippets.extend(code_snippets)

    # Display the discovered code blocks
    print(f"Found {len(all_code_snippets)} code snippet(s) on page {page_num}.\n")
    for idx, snippet in enumerate(all_code_snippets, start=1):
        print(f"--- Code Snippet #{idx} ---")
        print(snippet)
        print("--------------------------\n")


if __name__ == "__main__":
    main()
