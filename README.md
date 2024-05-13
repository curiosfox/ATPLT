# Final ATPLT Project for SRA memory model using C11 tester
## Description:
    This repository consists of the final project for Advanced topics in programming language theory which consists of verifying the consistency of programs in the C11 tester for the Strengthened Release-Acquire memory model. 

## Project structure:

    The Project structure consists of a c11 tester and a diff file, the project repository is to have a docker file but has been removed due to GitHub limits.

### C11 tester:

    The C11 tester has been modified and contains a test directory where the example programs are located and can be run from the test directory. 
    The program has a complied code using Clang and Clang++

### Steps to run the example code:

    The C code can be run using the below commands.
    
```pycon
./run.sh /test/<testfile> [options]
```
Note: The environment must be enabled to run these scripts such that we can compile and run them, but due to an issue with llvm installation we will use a docker image to run them

Step 1:
    Pull the docker image 
```pycon
docker import pldi23-179.docker pldi23-179
```
Step 2: Start a container:
```pycon
docker run -it pldi23-179 bash
```
Step 3 (optional): Compile the c11 tester (this will also be done when you start the container)
```pycon
sh /root/compile.sh
```

Step 4: Compile testing code
```pycon
/root/c11tester_evaluation/benchmarks/clang++ <example_program> -o /root/c11tester_evaluation/benchmarks/example.out
```

Step 5: run the c11 tester against your scripts
```pycon
./run.sh ./test/<testfile> 
```

