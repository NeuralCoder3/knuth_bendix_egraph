#!/usr/bin/env python3
"""
Convert egg files to rule format.
Converts rw!("name"; "pattern" => "replacement") to equality format.
"""

import re
import sys
from typing import List, Tuple, Optional, Dict


# Replacement dictionary for function names
FUNCTION_REPLACEMENTS = {
    '+': 'Add',
    '*': 'Mul', 
    '-': 'Sub',
    '/': 'Div',
    'pow': 'Pow',
    'sin': 'Sin',
    'cos': 'Cos',
    'ln': 'Ln',
    'd': 'D',
    'i': 'I'
}

# Replacement dictionary for constants
CONSTANT_REPLACEMENTS = {
    '0': 'Zero',
    '1': 'One',
    '-1': 'MinusOne',
    '2': 'Two'
}


def clean_variable(var: str) -> str:
    """Remove question marks from variables."""
    return var.replace('?', '')


def replace_constants(expr: str) -> str:
    """Replace numeric constants with symbolic names."""
    # Replace negative numbers first
    expr = expr.replace('-1', 'MinusOne')
    expr = expr.replace('-2', 'MinusTwo')
    
    # Then replace positive numbers
    expr = expr.replace('0', 'Zero')
    expr = expr.replace('1', 'One')
    expr = expr.replace('2', 'Two')
    
    return expr


def parse_lisp_expression(expr: str) -> str:
    """Parse Lisp-style expression and convert to function call notation."""
    expr = expr.strip()
    
    # Handle simple cases (variables, constants)
    if not expr.startswith('('):
        cleaned = clean_variable(expr)
        return replace_constants(cleaned)
    
    # Apply constant replacement to the entire expression first
    expr = replace_constants(expr)
    
    # Remove outer parentheses
    expr = expr[1:-1].strip()
    
    # Find function name (first token)
    tokens = expr.split()
    if not tokens:
        return expr
    
    func_name = tokens[0]
    
    # Apply function name replacement
    if func_name in FUNCTION_REPLACEMENTS:
        func_name = FUNCTION_REPLACEMENTS[func_name]
    
    # Handle the rest as arguments
    if len(tokens) == 1:
        return f"{func_name}()"
    
    # Reconstruct the arguments part
    args_part = ' '.join(tokens[1:])
    
    # Parse arguments recursively
    args = parse_arguments(args_part)
    
    return f"{func_name}({', '.join(args)})"


def parse_arguments(args_str: str) -> List[str]:
    """Parse comma-separated arguments, handling nested parentheses."""
    args = []
    current_arg = ""
    paren_count = 0
    
    for char in args_str:
        if char == '(':
            paren_count += 1
            current_arg += char
        elif char == ')':
            paren_count -= 1
            current_arg += char
        elif char == ' ' and paren_count == 0:
            # Space at top level - potential argument separator
            if current_arg.strip():
                args.append(parse_lisp_expression(current_arg.strip()))
                current_arg = ""
        else:
            current_arg += char
    
    # Add the last argument
    if current_arg.strip():
        args.append(parse_lisp_expression(current_arg.strip()))
    
    return args


def extract_rw_rules(content: str) -> List[Tuple[str, str]]:
    """Extract all rw! rules from content, handling multi-line rules."""
    # Remove comments first
    content = re.sub(r'//.*$', '', content, flags=re.MULTILINE)
    
    # Pattern to match rw! rules, including multi-line ones
    # This pattern matches the entire rw! macro including multi-line strings
    pattern = r'rw!\s*\(\s*"[^"]*"\s*;\s*"([^"]*)"\s*=>\s*"([^"]*)"'
    
    rules = []
    matches = re.finditer(pattern, content, re.DOTALL)
    
    for match in matches:
        left_pattern = match.group(1).strip()
        right_pattern = match.group(2).strip()
        
        # Clean up multi-line strings
        left_pattern = re.sub(r'\s+', ' ', left_pattern)
        right_pattern = re.sub(r'\s+', ' ', right_pattern)
        
        rules.append((left_pattern, right_pattern))
    
    return rules


def convert_single_term(term: str) -> str:
    """Convert a single Lisp-style term to function call notation."""
    return parse_lisp_expression(term)


def convert_egg_file(input_file: str, output_file: str):
    """Convert egg file to rule format."""
    with open(input_file, 'r') as f:
        content = f.read()
    
    # Extract all rw! rules
    rules_data = extract_rw_rules(content)
    rules = []
    
    for left, right in rules_data:
        # Convert both sides to function call notation
        left_clean = parse_lisp_expression(left)
        right_clean = parse_lisp_expression(right)
        rules.append(f"{left_clean} = {right_clean}")
    
    # Write output
    with open(output_file, 'w') as f:
        for rule in rules:
            f.write(rule + '\n')
    
    print(f"Converted {len(rules)} rules from {input_file} to {output_file}")


def main():
    if len(sys.argv) < 2:
        print("Usage:")
        print("  python convert_egg.py <input.egg> <output.rule>  # Convert egg file")
        print("  python convert_egg.py --term <lisp_expression>   # Convert single term")
        sys.exit(1)
    
    if sys.argv[1] == "--term":
        if len(sys.argv) != 3:
            print("Usage: python convert_egg.py --term <lisp_expression>")
            sys.exit(1)
        
        term = sys.argv[2]
        try:
            converted = convert_single_term(term)
            print(f"Input:  {term}")
            print(f"Output: {converted}")
        except Exception as e:
            print(f"Error: {e}")
            sys.exit(1)
    else:
        if len(sys.argv) != 3:
            print("Usage: python convert_egg.py <input.egg> <output.rule>")
            sys.exit(1)
        
        input_file = sys.argv[1]
        output_file = sys.argv[2]
        
        try:
            convert_egg_file(input_file, output_file)
        except FileNotFoundError:
            print(f"Error: File {input_file} not found")
            sys.exit(1)
        except Exception as e:
            print(f"Error: {e}")
            sys.exit(1)


if __name__ == "__main__":
    main()
