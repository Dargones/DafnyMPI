# DafnyMPI is a Dafny Library for Verifying Message-Passing Concurrent Programs

[Link to repository](https://github.com/Dargones/DafnyMPI/tree/main)

# Table of Contents:

- [DafnyMPI is a Dafny Library for Verifying Message-Passing Concurrent Programs](#dafnympi-is-a-dafny-library-for-verifying-message-passing-concurrent-programs)
- [Table of Contents:](#table-of-contents)
  - [1. Introduction](#1-introduction)
  - [2. Hardware Dependencies](#2-hardware-dependencies)
  - [3. Getting Started Guide](#3-getting-started-guide)
    - [3.1 (Alternative, Not Recommended) Native Installation on MacOS](#31-native-installation-on-macos)
  - [4. Step-by-Step Instructions](#4-step-by-step-instructions)
    - [4.1. Verification, Compilation, and a Demo](#41-verification-compilation-and-a-demo)
    - [4.2. Verification Time and Line Count (Table 3)](#42-verification-time-and-line-count-table-3)
    - [4.3. Running Time Evaluation (Figure 7)](#43-running-time-evaluation-figure-7)
  - [5. Repository File Index](#5-repository-file-index)

## 1. Introduction

This repository hosts DafnyMPI, a library for verifying MPI concurrent code
in [Dafny](https://github.com/dafny-lang/dafny/tree/master). 
The repository contains the sources code for DafnyMPI and all the
benchmarks discussed in the accompanying paper (accepted to POPL 2026, 
co-authored by Aleksandr Fedchin, Antero Mejr, Jeffrey S. Foster, and Hari Sundar, 
will link to preprint soon). 
This code is also available
as an artifact on [Zenodo](https://doi.org/10.5281/zenodo.17102521).

## 2. Hardware Dependencies

A machine with 8GB+ of RAM and 3+ logical CPU cores running MacOS or Ubuntu should be 
sufficient to use DafnyMPI and replicate the key findings of the paper. To fully 
replicate the [results of Figure 7](#43-running-time-evaluation-figure-7), 
the machine must also have 16+ logical CPUs (slots).  

We have built DafnyMPI natively on MacOS and tested DafnyMPI using Docker on the following machines:
- An M3 Mac machine with 48GB of memory (of which Docker was allowed to use 8GB)
- A Dell machine running Ubuntu 22.04 with 36GB of memory 

This repository also uses GitHub's default macos-latest configuration to test updates on each commit. 
(except for replicating the results of Figure 7 from the paper, which requires 16+ CPU cores.)

## 3. Getting Started Guide

To set up DafnyMPI with Docker (recommended for replicating the results of the paper), please follow these instructions:

### Step 1. Install Docker Engine. 

See [https://docs.docker.com/engine/install/](https://docs.docker.com/engine/install/) 
for instructions. Please check in the Docker settings that the Memory Limit is 
set to 8GB or more. If you are using Ubuntu, Docker should automatically allow 
itself to use as much memory as your machine has available. If you are running 
Docker Desktop, we recommend increasing the Memory Limit and Swap space in 
Docker Settings if your host machine allows it, although 8GB should be 
sufficient for reproducing results of the paper. Please also increase the 
number of CPU cores available to Docker to 16 or more if you wish to run the 
compiled versions of our benchmarks.

### Step 2. Build Dockerfile

Make sure Docker daemon is running (e.g., by launching Docker app).
Next, open the Terminal and navigate to the root directory of this repository. 
When building on an AMD64-based machine, run:
```sh
docker build -t dafnympi .
```

Otherwise, if on ARM-based machine, run:
```sh
docker buildx build --platform=linux/amd64 -t dafnympi .
```

When runnign on ARM, please make sure to specify `--platform=linux/amd64` as 
above, this is needed because Z3 4.12.1, which Dafny 4.10 uses as a backend, 
is not available for ARM-based linux machines.

You only need to run the above command once. The command installs Dotnet, 
OpenMPI, Python, and all relevant Python packages.

### Step 3. Launch Interactive Shell

To obtain an interactive shell in the container:

If on AMD64, run:

```sh
docker run --rm -it \
  -v "$PWD:/dafnympi" -w /dafnympi \
  dafnympi bash
```

If on ARM, run:
```sh
docker run --rm -it --platform=linux/amd64 \
  -v "$PWD:/dafnympi" -w /dafnympi \
  dafnympi bash
```

### Step 4. Build Dafny

To use DafnyMPI, you must first build Dafny 4.10. 
To build Dafny, run the following command. You do not need to build Dafny
again if you relaunch the shell. Please allow this step a few minutes as it can 
take longer, especially if you are running docker on an ARM-based machine.

```sh
make docker
```

### Step 5. Verify Installation
 To verify your installation, run Dafny like so:
```sh
dotnet dafny/Binaries/Dafny.dll verify --standard-libraries src/Example/Example.dfy
```

If your installation was successful, you will see the following output:

```dafny
Dafny program verifier finished with 3 verified, 0 errors
```

### 3.1. Native Installation on MacOS

To install DafnyMPI natively on MacOS, please make sure 
you have Dotnet 8 installed, then run `make install-dependencies-mac-arm` to 
install open MPI and all necessary python packages. Finally, run `make mac-arm` 
to build Dafny 4.10. Note that using a different version of Dafny is likely to 
break DafnyMPI verification.

If you encounter the `externally-managed-environment` error during the 
`make install-dependencies-mac-arm` step, this likely means that your Python 
 installation is managed by Homebrew. Please activate a conda environment 
 instead, or install via Docker as described above.
 
## 4. Step-by-Step Instructions

In what follows, we describe how to reproduce all the figures and, by extension, 
the findings of the accompanying paper. Note that all the figures produced while
 running Docker shell will also be saved inside the repository root folder on 
 your host machine (so you can open and view them from outside Docker).

### 4.1. Verification, Compilation, and a Demo

To verify all the files in the project please run `make verify`. Please note that
low CPU speeds may lead to verification timeouts on certain parts of the Heat 
and Poisson benchmark. However, we have configured DafnyMPI so that it 
succesfully verifies on GitHub's default macos-latest configuration and our 
personal machines (as you can see in our workflows), 
so it is highly unlikely that you enounter this issue unless 
you are using a different version of Dafny or Z3. If you do run into timeouts,
we recommend increasing the `--verification-time-limit` value in the Makefile.

When succesfull, you will see the following output after 5-15 minutes:

```
dotnet dafny/Binaries/Dafny.dll verify --verification-time-limit 90 --standard-libraries $(find src/DafnyMPI -name "*.dfy")

Dafny program verifier finished with 339 verified, 0 errors
dotnet dafny/Binaries/Dafny.dll verify --verification-time-limit 90 --standard-libraries $(find src/Example -name "*.dfy")

Dafny program verifier finished with 3 verified, 0 errors
dotnet dafny/Binaries/Dafny.dll verify --verification-time-limit 90 --standard-libraries $(find src/LinearConvection -name "*.dfy")

Dafny program verifier finished with 34 verified, 0 errors
dotnet dafny/Binaries/Dafny.dll verify --verification-time-limit 90 --standard-libraries $(find src/Poisson -name "*.dfy")

Dafny program verifier finished with 2495 verified, 0 errors
dotnet dafny/Binaries/Dafny.dll verify --verification-time-limit 90 --standard-libraries $(find src/Heat -name "*.dfy")

Dafny program verifier finished with 2403 verified, 0 errors
```

To compile the code, please run `make compile-python`. 
This step shoudl take 1-2 minutes.

You can now verify that the code has been compiled successully by running, 
for example, `make time-heat`, which will run sequential and parallel versions 
of the corresponding benchmark while only using 3 CPU cores. In the output, you 
should be able to see that the parallal version (second) is faster:

```
time python3 src/Heat/Sequential-py/__main__.py 128 50 false
53.01user 0.09system 0:49.34elapsed 107%CPU (0avgtext+0avgdata 83700maxresident)k
67224inputs+900outputs (140major+21809minor)pagefaults 0swaps
time mpiexec -n 3 python3 src/Heat/Parallel-py/__main__.py 128 50 false
62.54user 0.43system 0:20.29elapsed 310%CPU (0avgtext+0avgdata 100528maxresident)k
34176inputs+18488outputs (192major+53324minor)pagefaults 0swaps
```

### 4.2. Verification Time and Line Count (Table 3)

This step should take approximately 10 minutes.

To reproduce Table 3 of the paper, please run `python3 src/Scripts/table3.py`. 
The script will re-verify all files and produce a table formatted using LaTeX 
with all relevant information.

The output should look like this (verification times may differ per machine):

```
\begin{table}[tb]
\centering{\setlength{\tabcolsep}{4pt}
\caption{Number of lines of code (LOC) and verification time as measures of proof complexity.}
\begin{tabular}{|l|r|r|r|r|r|r|r|r|r|r|r||r|}
\hline
\multirow{2}{*}{} & \multicolumn{3}{|c|}{Linear Convection} & \multicolumn{4}{|c|}{Poisson} & \multicolumn{4}{|c||}{Heat Diffusion} & \multirow{2}{*}{Total} \\
\cline{2-12}
 & Spec & Seq & Par & Spec & Shared & Seq & Par & Spec & Shared & Seq & Par &  \\ \hline\hline
LOC & 209 & 106 & 379 & 384 & 126 & 153 & 1626 & 328 & 406 & 137 & 1516 & 5370 \\ \hline
\% Ghost & 100 & 45 & 65 & 100 & 72 & 55 & 91 & 100 & 81 & 57 & 89 & 87 \\ \hline
Time to & \multirow{2}{*}{3} & \multirow{2}{*}{3} & \multirow{2}{*}{25} & \multirow{2}{*}{4} & \multirow{2}{*}{6} & \multirow{2}{*}{4} & \multirow{2}{*}{148} & \multirow{2}{*}{3} & \multirow{2}{*}{11} & \multirow{2}{*}{4} & \multirow{2}{*}{154} & \multirow{2}{*}{371} \\
verify (s) & \rule{0pt}{2.2ex} & \rule{0pt}{2.2ex} & \rule{0pt}{2.2ex} & \rule{0pt}{2.2ex} & \rule{0pt}{2.2ex} & \rule{0pt}{2.2ex} & \rule{0pt}{2.2ex} & \rule{0pt}{2.2ex} & \rule{0pt}{2.2ex} & \rule{0pt}{2.2ex} & \rule{0pt}{2.2ex} & \rule{0pt}{2.2ex} \\ \hline
\end{tabular}
\label{tab:effort}
}
\end{table}
```

### 4.3. Running Time Evaluation (Figure 7)

To reproduce the plots in Figure 7, please run `python3 src/Scripts/figure7.py`.
This script will create PDF files with figures and place then in the root 
directory of the project.

By default, the script uses the cached results from the previous run. 
If you wish to rerun the experiments, please remove the cached_results.txt file. 

To reproduce Figure 7 in full, your machine must have 16+ logical CPUs (slots) and Docker/MPI 
should have access to 16+ of these.
To make sure the latter is the case on MacOS, go to Settings->Resources and asjust the CPU limit.
On Ubuntu, you may need to add `--cpus=16` argument when calling `docker run`.
If you don't have 16+ CPUs, you can edit the `cached_results.txt` file and only keep 
the lines where `n_procs` is greater than your machine allows. 
Then run `python3 src/Scripts/figure7.py` and the script will redo all the experiments 
that are possible on your machine.

### 5. Repository File Index

This repository contains the following files:

- `dafny` directory contains Dafny 4.10.
- `src` directory contains all the code written for this project, including:
  - `DafnyMPI` - the source code for DafnyMPI library.
  - `Heat`, `LinearConvection`, and `Poisson` - the three benchmarks.
  - `Scripts` - python scripts used to automate evaluation.
`cached_results.txt` caches the results of experiments used for Figure 7. 
Remove this file if you wish to redo all the experiments.
- `LICENSE.txt` file with MIT License
- `README.md` is this file.
- `Makefile` allows building Dafny
- `Dockerfile` allows building and all necessary dependencies on most UNIX 
systmes using Docker.
