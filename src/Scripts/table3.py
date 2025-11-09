#!/usr/bin/env python3
import os
import sys
from collections import OrderedDict
import time
import subprocess

from linecounter import measure_dafny_ghost_code

def get_file_line_count(path):
    with open(path, 'r', encoding='utf-8') as f:
        return sum(1 for _ in f)


def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    root_dir = os.path.abspath(os.path.join(script_dir, os.pardir))

    DAFNYMPI = "DafnyMPI"
    LC = 'Linear Convection'
    POISSON = 'Poisson'
    HEAT = 'Heat Diffusion'
    SPEC = "Spec"
    SEQ = "Seq"
    PAR = "Par"
    SHARED = "Shared"
    CORE = "Core"
    ARRAYS = "Arrays"
    SKIP = ""
    TOTAL = "TOTAL"

    mapping = {
        'Example/Example.dfy': (SKIP, SKIP),
        'DafnyMPI/Utils.dfy': (SKIP, SKIP),
        'DafnyMPI/Externs/MPIResource.dfy': (SKIP, CORE),
        'DafnyMPI/Externs/ExternUtils.dfy': (SKIP, SKIP),
        'DafnyMPI/Externs/MPI.dfy': (SKIP, CORE),
        'DafnyMPI/Arrays1D.dfy': (SKIP,  ARRAYS ),
        'DafnyMPI/Arrays2D.dfy': (SKIP,  ARRAYS ),
        'LinearConvection/Spec.dfy': (LC,  SPEC),
        'LinearConvection/Sequential.dfy': (LC, SEQ),
        'LinearConvection/Parallel.dfy': (LC, PAR),
        'Poisson/Spec.dfy': (POISSON,  SPEC),
        'Poisson/Shared.dfy': (POISSON, SHARED),
        'Poisson/Sequential.dfy': (POISSON, SEQ),
        'Poisson/Parallel.dfy': (POISSON, PAR),
        'Poisson/SequentialBackend.dfy' : (POISSON, SEQ),
        'Poisson/ParallelBackend.dfy' : (POISSON, PAR),
        'Heat/Spec.dfy': (HEAT,  SPEC),
        'Heat/RK4Impl.dfy': (HEAT, SHARED),
        'Heat/SequentialBackend.dfy' : (HEAT, SEQ),
        'Heat/ParallelBackend.dfy' : (HEAT, PAR),
        'Heat/Sequential.dfy': (HEAT, SEQ),
        'Heat/Parallel.dfy': (HEAT, PAR),
    }

    categories = OrderedDict()
    for rel_path, (cat, sub) in mapping.items():
        categories.setdefault(cat, []).append(sub)
    for cat, subs in categories.items():
        seen = []
        for s in subs:
            if s not in seen:
                seen.append(s)
        categories[cat] = seen
    categories[TOTAL] = [TOTAL]

    counts = {cat: {sub: 0 for sub in subs} for cat, subs in categories.items()}
    ghost_counts = {cat: {sub: 0 for sub in subs} for cat, subs in categories.items()}
    normal_counts = {cat: {sub: 0 for sub in subs} for cat, subs in categories.items()}
    file_paths = {cat: {sub: [] for sub in subs} for cat, subs in categories.items()}

    total_ghost_check = 0
    unmatched = []
    for dirpath, _, filenames in os.walk(root_dir):
        for fn in filenames:
            if fn.endswith('.dfy'):
                full_path = os.path.join(dirpath, fn)
                rel = os.path.relpath(full_path, root_dir).replace(os.sep, '/')
                if rel in mapping:
                    cat, sub = mapping[rel]
                    if cat == SKIP or sub == SKIP:
                        continue
                    count = get_file_line_count(full_path)
                    counts[cat][sub] += count
                    counts[TOTAL][TOTAL] += count
                    ghost, normal = measure_dafny_ghost_code(full_path)
                    ghost_counts[TOTAL][TOTAL] += ghost 
                    normal_counts[TOTAL][TOTAL] += normal
                    ghost_counts[cat][sub] += ghost
                    normal_counts[cat][sub] += normal
                    file_paths[cat][sub].append(os.path.join(root_dir, rel))
                else:
                    unmatched.append(rel)

    del categories[SKIP]
    del counts[SKIP]
    del ghost_counts[SKIP]
    del normal_counts[SKIP]
    del file_paths[SKIP]

    total_ghost = 0
    for cat in categories:
        for sub in categories[cat]:
            if cat == TOTAL or sub == TOTAL:
                continue
            total_ghost += counts[cat][sub]
            total_ghost_check += counts[cat][sub] * ghost_counts[cat][sub] / (
                ghost_counts[cat][sub] + normal_counts[cat][sub])
    print(f"Total diff: {total_ghost_check / total_ghost} vs {ghost_counts[TOTAL][TOTAL] / (ghost_counts[TOTAL][TOTAL] + normal_counts[TOTAL][TOTAL])}")
    print(f"Total count diff: {total_ghost} vs {counts[TOTAL][TOTAL]}")

    if unmatched:
        sys.exit("Error: Unmatched files found:\n" + "\n".join(unmatched))

    verify_times = {cat: {sub: 0.0 for sub in subs} for cat, subs in categories.items()}
    for cat in categories:
        for sub in categories[cat]:
            files = file_paths[cat][sub]
            if files:
                start = time.time()
                command = ["dotnet", f"{root_dir}/../dafny/Binaries/Dafny.dll", "verify", "--standard-libraries", "--verification-time-limit", "90"] + files
                print("Executing: " + " ".join(command))
                subprocess.run(command,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                end = time.time()
                verify_times[cat][sub] = end - start
                verify_times[TOTAL][TOTAL] += end - start

    total_cols = sum(len(subs) for subs in categories.values())
    col_format = "|l|" + "r|" * total_cols
    # col_format = "|@{\hspace{0.4em}}l@{\hspace{0.4em}}|" + "@{\hspace{0.4em}}r@{\hspace{0.4em}}|" * total_cols

    print("\\begin{table}[tb]")
    print("\\centering{\\setlength{\\tabcolsep}{4pt}")
    print("\\caption{Number of lines of code (LOC) and verification time as measures of proof complexity.}")
    print(f"\\begin{{tabular}}{{{col_format}}}")
    print("\\hline")

    # center = "|@{\hspace{0.4em}}c@{\hspace{0.4em}}|"
    center = "|c|"

    spans = [f"\\multicolumn{{{len(subs)}}}{{{center}}}{{{cat}}}" for cat, subs in categories.items()]
    print(" & ".join(["\\multirow{2}{*}{}"] + spans[:-1] + ["\\multirow{2}{*}{Total}"]) + " \\\\")

    print(f"\\cline{{2-{total_cols}}}")

    subs_flat = [sub for subs in categories.values() for sub in subs]
    print(" & " + " & ".join(subs_flat[:-1] + [""]) + " \\\\ \\hline\\hline")

    row_vals = [str(counts[cat][sub]) for cat in categories for sub in categories[cat]]
    print("LOC & " + " & ".join(row_vals) + " \\\\ \\hline")

    percent_vals = []
    for cat in categories:
        for sub in categories[cat]:
            g = ghost_counts[cat][sub]
            n = normal_counts[cat][sub]
            total = g + n
            percent = f"{int((100 * g / total))}" if total > 0 else "0"
            percent_vals.append(percent)
    print("\\% Ghost & " + " & ".join(percent_vals) + " \\\\ \\hline")

    verify_vals = [f"{int(verify_times[cat][sub])}" for cat in categories for sub in categories[cat]]
    print("Time to & " + 
          " & ".join(f"\\multirow{{2}}{{*}}{{{t}}}" for t in verify_vals) + r" \\")
    print("verify (s) & " +
          " & ".join(r"\rule{0pt}{2.2ex}" for _ in verify_vals) + r" \\ \hline")

    print("\\end{tabular}")
    print("\\label{tab:effort}")
    print("}")
    print("\\end{table}")

if __name__ == "__main__":
    main()
