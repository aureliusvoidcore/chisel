#!/usr/bin/env python3
"""
Inline verification properties from separate modules into the main module.
This transforms separate verification modules that reference hierarchical signals
into inline properties within the main module.
"""

import sys
import re

def inline_verification_modules(sv_file):
    with open(sv_file, 'r') as f:
        lines = f.readlines()
    
    main_module_name = None
    main_module_end = -1
    verification_props = []
    in_verif_module = False
    skip_module = False
    
    # First pass: find main module and extract properties
    for i, line in enumerate(lines):
        # Find main module name and end
        m = re.match(r'module\s+(\w+)\s*\(', line)
        if m and not main_module_name:
            main_module_name = m.group(1)
        
        if main_module_name and line.strip() == 'endmodule' and main_module_end < 0:
            main_module_end = i
        
        # Detect verification modules
        if main_module_name and re.match(rf'module\s+{main_module_name}_Verification', line):
            in_verif_module = True
            skip_module = False
            continue
        
        if in_verif_module and line.strip() == 'endmodule':
            in_verif_module = False
            skip_module = True
            continue
        
        # Extract properties and transform hierarchical references
        if in_verif_module:
            # Transform ShiftRegister.signal to signal
            transformed = re.sub(rf'{main_module_name}\.(\w+)', r'\1', line)
            # Skip empty lines and module declarations
            if transformed.strip() and not transformed.strip().startswith('module'):
                verification_props.append(transformed)
    
    if main_module_end < 0:
        print(f"Error: Could not find end of main module {main_module_name}")
        return False
    
    # Second pass: write output with inlined properties
    output_lines = []
    skip_until_endmodule = False
    skip_bind_section = False
    
    for i, line in enumerate(lines):
        # Skip bind/include sections after first endmodule
        if i > main_module_end:
            if '// ----- 8< ----- FILE' in line or '`include' in line or '`ifndef' in line or '`define' in line or '`endif' in line or 'bind ' in line:
                skip_bind_section = True
                continue
        
        # Skip verification modules
        if main_module_name and re.match(rf'module\s+{main_module_name}_Verification', line):
            skip_until_endmodule = True
            continue
        
        if skip_until_endmodule:
            if line.strip() == 'endmodule':
                skip_until_endmodule = False
                # Skip empty lines after
                continue
            continue
        
        # Insert properties before main module endmodule
        if i == main_module_end:
            if verification_props:
                output_lines.append('\n  // Inlined verification properties\n')
                output_lines.extend(verification_props)
                output_lines.append('\n')
        
        output_lines.append(line)
    
    # Write back
    with open(sv_file, 'w') as f:
        f.writelines(output_lines)
    
    print(f"Inlined {len(verification_props)} verification properties into {main_module_name}")
    return True

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <systemverilog_file>")
        sys.exit(1)
    
    if not inline_verification_modules(sys.argv[1]):
        sys.exit(1)
