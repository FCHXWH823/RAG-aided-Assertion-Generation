import fitz  # PyMuPDF

# --------------------------------------
# 1) Helpers for detecting "code" lines
# --------------------------------------

def is_code_font(font_name):
    """
    Simple heuristic: if the font name suggests a monospaced / code font.
    Adjust for your PDF's fonts as needed.
    """
    if not font_name:
        return False
    mono_keywords = ["Courier", "Mono", "Consolas", "Code", "Menlo", "LucidaConsole"]
    f_lower = font_name.lower()
    return any(kw.lower() in f_lower for kw in mono_keywords)

def is_single_number(text):
    """
    Returns True if 'text' is just a single integer, e.g. "12".
    """
    text = text.strip()
    if not text.isdigit():
        return False
    # Extra check: ensure it's purely numeric. 
    # If you want to allow '1:' or something, adapt accordingly.
    return True

def is_code_or_linenum_line(line):
    """
    Returns True if this line is EITHER a code line or a single line index.
    - Code line => all spans use monospaced fonts (or you can define other checks).
    - Single number => line is just an integer, e.g. "12".
    """
    # Flatten spans' text
    line_text = "".join(span.get("text", "") for span in line.get("spans", [])).strip()
    if is_single_number(line_text):
        return True

    # Check if every span is code
    spans = line.get("spans", [])
    if not spans:
        return False

    # If you only require that *any* span is monospaced, adapt the logic
    # Here we say *all* spans must be monospaced to treat the entire line as code
    for span in spans:
        fontname = span.get("font", "")
        # new added
        if "ut" in span.get("text"):
            continue
        if not is_code_font(fontname):
            return False
    return True

# --------------------------------------
# 2) Classify blocks: code or text
# --------------------------------------

def classify_block(block):
    """
    Classify a block as 'code' or 'text', based on the rule:
    - code if EVERY line is either code or a single number
    - else text
    """
    if "lines" not in block:
        return "text"  # no lines => treat as text or ignore?

    lines = block["lines"]
    for line in lines:
        if not is_code_or_linenum_line(line):
            return "text"
    return "code"

# --------------------------------------
# 3) Accumulate consecutive code blocks
#    & remove line indexes
# --------------------------------------

def accumulate_code_blocks(blocks):
    """
    1. If we see consecutive 'code' blocks, merge them into one 'big code block'.
    2. Remove lines that are ONLY a single number (the line index).
    Returns a new list of blocks with code blocks merged and cleaned.
    """
    merged = []
    current_code_block = None

    for block in blocks:
        btype = block["type"]  # we stored 'type' as either "code" or "text"
        if btype == "code":
            # If we're currently accumulating code, merge
            if current_code_block is None:
                # create new code block
                current_code_block = {
                    "bbox": list(block["bbox"]),  # clone
                    "lines": [],
                    "type": "code"
                }
            else:
                # expand bbox to cover both
                x0a, y0a, x1a, y1a = current_code_block["bbox"]
                x0b, y0b, x1b, y1b = block["bbox"]
                current_code_block["bbox"] = [
                    min(x0a, x0b),
                    min(y0a, y0b),
                    max(x1a, x1b),
                    max(y1a, y1b),
                ]
            # Add lines (excluding single-number lines)
            for line in block["lines"]:
                line_text = "".join(s.get("text","") for s in line.get("spans",[])).strip()
                if not is_single_number(line_text):
                    # keep this line
                    current_code_block["lines"].append(line)
        else:
            # It's a text block
            # if we have an open code block, flush it
            if current_code_block is not None:
                merged.append(current_code_block)
                current_code_block = None
            # Then add this text block as-is
            merged.append(block)

    # If there's a code block open at the end, flush it
    if current_code_block is not None:
        merged.append(current_code_block)

    return merged

# --------------------------------------
# 4) Merge a single-line indentation block
#    with the subsequent text block
# --------------------------------------

def is_indentation_line(line):
    """
    Heuristic: a line that starts with spaces or we can check if x0 is bigger than some threshold.
    We'll do a simple check here: if it starts with 2 or more spaces => indentation line.
    Adjust to your scenario.
    """
    # text = "".join(span.get("text","") for span in line.get("spans",[])).rstrip("\n\r")
    x0, y0, x1, y1 = line["bbox"]
    return x0 > 65
    # return text.startswith("  ")  # e.g. 2 leading spaces


def block_to_text(block):
    """
    Given one merged block dict with a 'lines' key, convert
    it into a multi-line text string.
    """
    lines_flat = []
    for ln in block["lines"]:
        ln_text = "".join(sp.get("text","") for sp in ln.get("spans",[])).strip()
        lines_flat.append(ln_text)
    if block["type"] == 'code':
        block_text = "\n".join(lines_flat)
    else:
        block_text = " ".join(lines_flat)

    return block_text

def merge_indentation_blocks(blocks):
    """
    If a text block is a single line and that line is 'indented',
    merge it with the next text block. 
    Returns a new list of blocks.
    """
    new_blocks = []
    skip_next = False

    for i in range(len(blocks)):
        if skip_next:
            skip_next = False
            continue

        block = blocks[i]
        if block["type"] != "text":
            # code block => just keep it
            new_blocks.append(block)
            continue

        lines = block.get("lines", [])
        # Check if single line + is_indentation_line => merge with next text block
        if is_indentation_line(block):
            # Look ahead to next block if it exists and is also text
            if i+1 < len(blocks):
                next_block = blocks[i+1]
                if next_block["type"] == "text" and not is_indentation_line(next_block):
                    # Merge them
                    merged_block = {
                        "bbox": [
                            min(block["bbox"][0], next_block["bbox"][0]),
                            min(block["bbox"][1], next_block["bbox"][1]),
                            max(block["bbox"][2], next_block["bbox"][2]),
                            max(block["bbox"][3], next_block["bbox"][3]),
                        ],
                        "lines": block["lines"] + next_block["lines"],
                        "type": "text"
                    }
                    new_blocks.append(merged_block)
                    skip_next = True
                else:
                    # Next block isn't text => can't merge
                    new_blocks.append(block)
            else:
                # There's no next block => can't merge
                new_blocks.append(block)
        else:
            # Not a single indentation line
            new_blocks.append(block)

    return new_blocks

# --------------------------------------
# Bringing it all together in a main
# --------------------------------------

def process_page_for_codeblocks(page):
    """
    Performs the required steps on a single PyMuPDF 'page':
      1) Get each block
      2) Classify as code or text
      3) Accumulate continuous code blocks, removing line indexes
      4) Merge single-line indentation blocks with subsequent text
    Returns a final list of blocks with code blocks and text blocks.
    """
    page_dict = page.get_text("dict")
    raw_blocks = page_dict.get("blocks", [])

    # Some blocks might have no 'lines' (image blocks, etc.), let's keep them as text for now
    blocks = []
    for b in raw_blocks:
        if "lines" in b and b["lines"]:
            # classify
            block_type = classify_block(b)
            blocks.append({
                "bbox": b["bbox"],
                "lines": b["lines"],
                "type": block_type
            })
        # else:
        #     # keep it but treat as text or ignore
        #     blocks.append({
        #         "bbox": b["bbox"],
        #         "lines": [],
        #         "type": "text"
        #     })

    # Step 3: Accumulate consecutive code blocks => remove single-number lines
    merged_code = accumulate_code_blocks(blocks)

    # Step 4: Merge single-line indentation blocks with subsequent text block
    final_blocks = merge_indentation_blocks(merged_code)

    if len(final_blocks):
        del final_blocks[0] # remove the first line of one page, which is just the page index and section name

    return final_blocks

# --------------------------------------
# Example usage
# --------------------------------------

def get_pdf_blocks(pdf_path):
    # pdf_path = "CernyDudani-SVA- The Power of Assertions in SystemVerilog.pdf"
    # page_num = 25

    doc = fitz.open(pdf_path)
    text_blocks = []
    for page_num in range(len(doc)):

        page = doc[page_num]

        final_blocks = process_page_for_codeblocks(page)

        text_blocks += final_blocks
        # Print results
        # We'll flatten each block's lines to text for demonstration

        # for idx, block in enumerate(final_blocks, start=1):
        #     block_type = block["type"]
        #     block_text = block_to_text(block)
        #     print(f"--- Block #{idx} --- [Type: {block_type}]")
        #     print(block_text)
        #     print("")
    
    return text_blocks

# if __name__ == "__main__":
#     main()
