import re
from pathlib import Path
import sys

def measure_dafny_ghost_code(file_path, printcolored=False):
    RED = "\033[91m"
    BLACK = "\033[0m"

    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    # Step 0: Clean up all `{:<word>}` annotations
    tag_pattern = re.compile(r'{:([^}]+)}')
    lines = [tag_pattern.sub(r'\1', line) for line in lines]

    # Step 1: Remove empty lines or lines with only whitespace
    non_empty_lines = [(i, line.rstrip()) for i, line in enumerate(lines) if line.strip()]

    filtered = []
    for idx, (orig_idx, line) in enumerate(non_empty_lines):
        s = line.strip()
        if idx == 0 and s.startswith('module'):
            continue
        if idx == len(non_empty_lines) - 1 and s == '}':
            continue
        if s.startswith('include') or s.startswith('import'):
            continue
        filtered.append((orig_idx, line))
    non_empty_lines = filtered
    
    line_status = ['normal'] * len(non_empty_lines)

    def find_block_bounds(start_index):
        """Find matching braces from start_index onwards."""
        open_count = 0
        for i in range(start_index, len(non_empty_lines)):
            open_count += non_empty_lines[i][1].count('{')
            open_count -= non_empty_lines[i][1].count('}')
            if open_count == 0:
                return i
        return len(non_empty_lines) - 1

    # Step 2: mark single-line ghost commands and spill over until "{"
    ghost_starters = ('invariant', 'requires', 'ensures', 'decreases', 'reads', 'modifies')
    idx = 0
    while idx < len(non_empty_lines):
        _, line = non_empty_lines[idx]
        if line.strip().startswith(ghost_starters):
            line_status[idx] = 'ghost'
            idx += 1
            # mark subsequent lines as ghost until we hit a line with '{'
            while idx < len(non_empty_lines):
                if '{' in non_empty_lines[idx][1]:
                    break
                line_status[idx] = 'ghost'
                idx += 1
        else:
            idx += 1

    # Step 3: mark ghost commands that last multiple lines until a ";"
    extended_ghost_starters = ('ghost var', 'Lemma')  # assert excluded
    for idx in range(len(non_empty_lines)):
        _, line = non_empty_lines[idx]
        stripped = line.strip()
        if stripped.startswith(extended_ghost_starters) or '.Lemma' in stripped:
            j = idx
            while j < len(non_empty_lines):
                line_status[j] = 'ghost'
                if ';' in non_empty_lines[j][1]:
                    break
                j += 1

    # Step 4: mark one line ghost commands
    ghost_starters = ("assert", "reveal")
    for idx, (_, line) in enumerate(non_empty_lines):
        if line.strip().startswith(ghost_starters):
            line_status[idx] = 'ghost'

    # Step 5: mark function, predicate, lemma, and assert blocks (unless extern)
    ghost_keywords = ['function', 'predicate', 'lemma', 'calc', 'assert']
    for i, line in non_empty_lines:
        if any(kw in line for kw in ghost_keywords) and 'extern' not in line:
            if '{' in line and ('assert' not in line or ";" not in line):
                end_index = find_block_bounds(non_empty_lines.index((i, line)))
                for j in range(non_empty_lines.index((i, line)), end_index + 1):
                    line_status[j] = 'ghost'
            elif ('assert' not in line or (";" not in line)):
                for k in range(non_empty_lines.index((i, line)) + 1, len(non_empty_lines)):
                    if ";" in non_empty_lines[k][1] and 'assert' in line:
                        break
                    if '{' in non_empty_lines[k][1]:
                        end_index = find_block_bounds(k)
                        for j in range(non_empty_lines.index((i, line)), end_index + 1):
                            line_status[j] = 'ghost'
                        break

        if re.match(r'^\s*assert\s*\{', line):
            end_index = find_block_bounds(non_empty_lines.index((i, line)))
            for j in range(non_empty_lines.index((i, line)), end_index + 1):
                line_status[j] = 'ghost'

    # Output
    ghost_lines = [line for idx, (i, line) in enumerate(non_empty_lines) if line_status[idx] == 'ghost']
    normal_lines = [line for idx, (i, line) in enumerate(non_empty_lines) if line_status[idx] != 'ghost']

    if printcolored:
      print("Ghost lines removed:", len(ghost_lines))
      print("Non-empty, non-ghost lines remaining:", len(normal_lines))
      print("\nCode with ghost lines highlighted:")

      for idx, (_, line) in enumerate(non_empty_lines):
          color = RED if line_status[idx] == 'ghost' else BLACK
          print(f"{color}{line}{BLACK}")
      print("Ghost lines removed:", len(ghost_lines))
      print("Non-empty, non-ghost lines remaining:", len(normal_lines))
    return len(ghost_lines), len(normal_lines)

if __name__ == "__main__":
    measure_dafny_ghost_code(sys.argv[1], True)