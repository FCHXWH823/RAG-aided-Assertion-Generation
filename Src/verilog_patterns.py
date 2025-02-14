# Author Derek Ekberg

"""Shared Verilog pattern definitions and utility functions."""

import re
from typing import List, Tuple

# Common Verilog/SystemVerilog keywords and constructs
VERILOG_PATTERNS = [
    # Module-level keywords
    r'\b(module|endmodule|package|endpackage|interface|endinterface)\b',

    # Process blocks
    r'(always|always_comb|always_ff|always_latch)\s*@?',
    r'initial\s+begin',

    # Port declarations
    r'\b(input|output|inout)\s+(\[\d+:\d+\])?\s*(wire|reg|logic)?\b',

    # Data types
    r'\b(reg|wire|logic|bit|byte|shortint|int|longint|integer|time|real|shortreal|string)\b',

    # Variable declarations
    r'(assign|parameter|localparam)\s+\w+',

    # SystemVerilog specific
    r'\b(struct|union|enum|typedef|class|endclass)\b',
    r'\b(program|endprogram|sequence|endsequence|property|endproperty)\b',
    r'\b(assert|assume|cover|restrict)\b',

    # Common operators
    r'(<=|===|!==|\|\||&&)',

    # Generate constructs
    r'\b(generate|endgenerate|for|if|else|case)\b',

    # Behavioral blocks
    r'(begin|end)\b',

    # SystemVerilog assertions
    r'@\s*\(',
    r'\|=>\s*##',
    r'\$past\s*\(',

    # Common system tasks
    r'\$(display|write|monitor|time|finish|stop)\b'
]


def is_likely_prose(text: str) -> bool:
    """Check if text segment is likely to be prose rather than code."""
    prose_patterns = [
        r'\b(the|and|or|in|to|that|for|is|are|on|with|as|this|these|those)\b',
        r'[.!?]\s+[A-Z]',  # Sentence boundaries
        r'\b[A-Z][a-z]+\b\s+\b[A-Z][a-z]+\b'  # Capitalized word pairs
    ]
    return any(re.search(pattern, text) for pattern in prose_patterns)


def split_mixed_content(line: str) -> List[Tuple[str, bool]]:
    """Split a line into alternating prose and code segments.
    Returns list of (text, is_code) tuples."""
    segments = []
    current_pos = 0
    in_quotes = False
    quote_char = None

    # Boundary markers for Verilog constructs
    boundary_markers = [
        (r'\binput\b', r'\b(wire|reg|logic)?\b'),
        (r'\boutput\b', r'\b(wire|reg|logic)?\b'),
        (r'\balways\b', r'\b(begin|@)\b'),
        (r'\bmodule\b', r'\bendmodule\b'),
        (r'\bassign\b', r'\b(=|<=)\b'),
    ]

    while current_pos < len(line):
        if line[current_pos] in '"\'`':
            if not in_quotes:
                in_quotes = True
                quote_char = line[current_pos]
            elif line[current_pos] == quote_char:
                in_quotes = False
            current_pos += 1
            continue

        if not in_quotes:
            for start_pattern, end_pattern in boundary_markers:
                start_match = re.search(start_pattern, line[current_pos:])
                if start_match:
                    start_idx = current_pos + start_match.start()

                    if start_idx > current_pos:
                        pre_text = line[current_pos:start_idx]
                        if pre_text.strip():
                            segments.append((pre_text, False))

                    end_match = re.search(end_pattern, line[start_idx:])
                    end_idx = len(line) if not end_match else start_idx + end_match.end()

                    code_segment = line[start_idx:end_idx]
                    segments.append((code_segment, True))
                    current_pos = end_idx
                    break
            else:
                if not segments or not segments[-1][1]:
                    segments.append((line[current_pos], False))
                else:
                    segments[-1] = (segments[-1][0] + line[current_pos], False)
                current_pos += 1
        else:
            if segments:
                segments[-1] = (segments[-1][0] + line[current_pos], segments[-1][1])
            else:
                segments.append((line[current_pos], False))
            current_pos += 1

    return segments