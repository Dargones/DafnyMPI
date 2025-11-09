#!/usr/bin/env python3
import subprocess
import time
import statistics
import os
import csv
import matplotlib.pyplot as plt
import argparse


plt.rcParams.update({
    'pdf.fonttype': 42,
    'ps.fonttype': 42,
    'font.family': 'serif',
    'text.usetex': False,
    'font.size': 25,
    'axes.labelsize': 25,
    'xtick.labelsize': 12,
    'ytick.labelsize': 12,
    'legend.fontsize': 12,
    'figure.titlesize': 22,
    'lines.linewidth': 2
})


ALL = "ALL"
ITERATIONS = "iters"
LENGTH = "length"
FULLNAME = "full_name"
ADJUST = "adjust"
PROCS = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
REPEATS = 3


BENCHMARKS = {
    "LC": {
        LENGTH:     1200,
        ITERATIONS: 300,
        FULLNAME:   "LinearConvection",
        ADJUST: lambda length, procs : 
          length if length % procs == 0 else length + (procs - length % procs)
    },
    "Heat": {
        LENGTH:     168,
        ITERATIONS: 20,
        FULLNAME:   "Heat",
        ADJUST: lambda length, procs : 
          length if (length - 8) % procs == 0 
                 else length + (procs - (length - 8) % procs)
    },
    "Poisson": {
        LENGTH:     62,
        ITERATIONS: 200,
        FULLNAME:   "Poisson",
        ADJUST: lambda length, procs : 
          length if (length - 2) % procs == 0 
                 else length + (procs - (length - 2) % procs)
    }
}


MPI_CMD = ["mpiexec", "--use-hwthread-cpus", "-n"]
CACHE_FILE = "cached_results.txt"
CACHE_HEADER = ["benchmark", "n_procs", "time"]


def ensure_cache():
    if not os.path.exists(CACHE_FILE):
        with open(CACHE_FILE, "w", newline='') as f:
            f.write(','.join(CACHE_HEADER) + '\n')


def load_cache():
    cache = {}
    if os.path.exists(CACHE_FILE):
        with open(CACHE_FILE, newline='') as f:
            reader = csv.DictReader(f)
            for row in reader:
                key = (row['benchmark'], int(row['n_procs']))
                cache[key] = float(row['time'])
    return cache


def update_cache(benchmark, n_procs, elapsed):
    with open(CACHE_FILE, "a", newline='') as f:
        f.write(','.join([benchmark, str(n_procs), str(elapsed)]) + '\n')


def time_run(cmd_base, cmd_args, repeats=REPEATS):
    times = []
    for _ in range(repeats):
        cmd = cmd_base + cmd_args
        print(f"Running: {' '.join(cmd)}", flush=True)
        start = time.time()
        subprocess.run(cmd, check=True)
        times.append(time.time() - start)
    return statistics.median(times)


def run_benchmark(benchmark, n_procs, cache):
    key = (benchmark, n_procs)
    if key in cache:
        print(f"Using cached {benchmark} result "
              f"for {n_procs} procs: {cache[key]:.4f}s")
        return cache[key]
    
    sequential_command = os.path.join(
        "src", BENCHMARKS[benchmark][FULLNAME], "Sequential-py", "__main__.py")
    parallel_command = os.path.join(
        "src", BENCHMARKS[benchmark][FULLNAME], "Parallel-py", "__main__.py")

    if n_procs == 1:
        elapsed = time_run(["python3", sequential_command], 
                           [str(BENCHMARKS[benchmark][LENGTH]), 
                            str(BENCHMARKS[benchmark][ITERATIONS]), "false"])
    else:
        length = BENCHMARKS[benchmark][ADJUST](
            BENCHMARKS[benchmark][LENGTH], n_procs)
        args = [str(n_procs), "python3", parallel_command,
                str(length),  
                str(BENCHMARKS[benchmark][ITERATIONS]), "false"]
        elapsed = time_run(MPI_CMD, args)

    update_cache(benchmark, n_procs, elapsed)
    print(f"{benchmark} result for {n_procs} procs: {elapsed:.4f}s")
    cache[key] = elapsed
    return elapsed


def plot_results(procs, times, seq_time, outfile):
    plt.figure(figsize=(8, 6))
    plt.plot(procs, times)
    plt.xlabel('Number of processes')
    plt.ylabel('Time (s)')
    plt.grid(True)
    plt.tight_layout()
    plt.savefig(outfile)
    print(f"Saved plot to {outfile}")


def run_experiment(benchmark, cache):
    times = []
    for p in PROCS:
        print(f"\nRunning {benchmark} with {p} proc(s)...", flush=True)
        times.append(run_benchmark(benchmark, p, cache))
    plot_results(PROCS, times, times[0], benchmark + ".pdf")


def main():
    parser = argparse.ArgumentParser(
        description="Compare benchmark runtime for different # of processes.")
    parser.add_argument(
        "--benchmark", choices=list(BENCHMARKS.keys()) + [ALL], default=ALL,
        help=f"Specify which benchmark to plot (default: {ALL})")
    args = parser.parse_args()

    ensure_cache()
    cache = load_cache()

    if args.benchmark == ALL:
        args.benchmark = list(BENCHMARKS.keys())
    else:
        args.benchmark = [args.benchmark]

    for benchmark in args.benchmark:
        run_experiment(benchmark, cache)

if __name__ == '__main__':
    main()
