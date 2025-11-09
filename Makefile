mac:
	cd dafny && make exe && make z3-mac
	echo 'export PATH="${PATH}:/dafny/Binaries/z3/bin"' >> ~/.zshrc
	echo 'export PATH="${PATH}:/dafny/Binaries/z3/bin"' >> ~/.bashrc
	echo 'export PATH="${PATH}:/dafny/Binaries/z3/bin"' >> ~/.bash_profile
	export PATH="${PATH}:/dafny/Binaries/z3/bin"

mac-arm:
	cd dafny && make exe && make z3-mac-arm
	echo 'export PATH="${PATH}:/dafny/Binaries/z3/bin"' >> ~/.zshrc
	export PATH="${PATH}:/dafny/Binaries/z3/bin"

docker:
	cd dafny && make exe && make z3-ubuntu
	echo 'export PATH="${PATH}:/dafny/Binaries/z3/bin"' >> ~/.bashrc
	export PATH="${PATH}:/dafny/Binaries/z3/bin"
	
ubuntu: docker-intel

ubuntu-arm: docker-arm

install-dependencies-mac-arm:
	brew install open-mpi
	python3 -m pip install mpi4py numpy matplotlib
	cd dafny && make exe && make z3-mac-arm

verify:
	dotnet dafny/Binaries/Dafny.dll verify --verification-time-limit 90 --standard-libraries $$(find src/DafnyMPI -name "*.dfy")
	dotnet dafny/Binaries/Dafny.dll verify --verification-time-limit 90 --standard-libraries $$(find src/Example -name "*.dfy")
	dotnet dafny/Binaries/Dafny.dll verify --verification-time-limit 90 --standard-libraries $$(find src/LinearConvection -name "*.dfy")
	dotnet dafny/Binaries/Dafny.dll verify --verification-time-limit 90 --standard-libraries $$(find src/Poisson -name "*.dfy")
	dotnet dafny/Binaries/Dafny.dll verify --verification-time-limit 90 --standard-libraries $$(find src/Heat -name "*.dfy")

compile-python:
	dotnet dafny/Binaries/Dafny.dll translate py --standard-libraries --include-runtime --no-verify src/LinearConvection/Sequential.dfy
	dotnet dafny/Binaries/Dafny.dll translate py --standard-libraries --include-runtime --no-verify src/LinearConvection/Parallel.dfy
	cp src/DafnyMPI/Externs/*.py src/LinearConvection/Sequential-py/
	cp src/DafnyMPI/Externs/*.py src/LinearConvection/Parallel-py/
	dotnet dafny/Binaries/Dafny.dll translate py --standard-libraries --include-runtime --no-verify src/Heat/Sequential.dfy
	dotnet dafny/Binaries/Dafny.dll translate py --standard-libraries --include-runtime --no-verify src/Heat/Parallel.dfy
	cp src/DafnyMPI/Externs/*.py src/Heat/Sequential-py/
	cp src/DafnyMPI/Externs/*.py src/Heat/Parallel-py/
	dotnet dafny/Binaries/Dafny.dll translate py --standard-libraries --include-runtime --no-verify src/Poisson/Sequential.dfy
	dotnet dafny/Binaries/Dafny.dll translate py --standard-libraries --include-runtime --no-verify src/Poisson/Parallel.dfy
	cp src/DafnyMPI/Externs/*.py src/Poisson/Sequential-py/
	cp src/DafnyMPI/Externs/*.py src/Poisson/Parallel-py/

time-lc:
	time python3 src/LinearConvection/Sequential-py/__main__.py 120 300 false
	time mpiexec -n 3 python3 src/LinearConvection/Parallel-py/__main__.py 120 300 false

time-poisson:
	time python3 src/Poisson/Sequential-py/__main__.py 62 200 false
	time mpiexec -n 3 python3 src/Poisson/Parallel-py/__main__.py 62 200 false

time-heat:
	time python3 src/Heat/Sequential-py/__main__.py 128 50 false
	time mpiexec -n 3 python3 src/Heat/Parallel-py/__main__.py 128 50 false

figures:
	mpiexec -n 12 python3 src/Heat/Parallel-py/__main__.py 128 0 true
	mpiexec -n 12 python3 src/Heat/Parallel-py/__main__.py 128 100 true
	mpiexec -n 12 python3 src/LinearConvection/Parallel-py/__main__.py 120 0 true
	mpiexec -n 12 python3 src/LinearConvection/Parallel-py/__main__.py 120 100 true
	mpiexec -n 12 python3 src/Poisson/Parallel-py/__main__.py 62 0 true
	mpiexec -n 12 python3 src/Poisson/Parallel-py/__main__.py 62 100 true
	python3 src/Scripts/figure7.py
	python3 src/Scripts/table3.py
