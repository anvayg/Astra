# Astra

Astra stands for Automatic Synthesis for Transducers. It contains the implementation of the algorithm presented 
in the FMCAD 22 paper [Synthesizing Tranducers from Complex Specifications](https://scholar.google.com/citations?view_op=view_citation&hl=en&user=kR6ogecAAAAJ&citation_for_view=kR6ogecAAAAJ:u-x6o8ySG0sC), 
as well as the experimental results.

### Dependencies and Installation

This is a Maven project that depends on the [symbolicautomata library](https://github.com/lorisdanto/symbolicautomata). It 
also makes use of the Z3 and CVC4 SMT solvers.

First, build the `symbolicautomata` library following the directions on the repository page. Make sure that `models` and `benchmarks` 
project are in your working set so that Astra can find them. The easiest way to build both `symbolicautomata` and Astra is by opening
them in Eclipse: go to import existing Maven project, and then click on update project.

The `lib` directory should include the dynamic libraries for z3 and the binary executable for cvc4.

z3 : You need to build z3 for JAVA api and copy your com.microsoft.z3.jar, libz3.dylib/so and libz3java.dylib/so into lib folder
CVC4 : you need to build CVC4 and copy the binary file CVC4 into lib folder.

Finally, make sure that the `LD_LIBRARY_PATH` (on Linux) or `DYLD_LIBRARY_PATH` (on MacOS) includes the `lib` directory.

### Running experiments

The synthesizer is in the `src/main/java` directory; the SMT encodings are in the subdirectory `solver`, while `automata` contains
the implementation of symbolic transducers and operations on symbolic automata and transducers.

The benchmarks are in the `src/test/java/benchmarks` directory. The main set of benchmarks is in the `Benchmarks` subdirectory. To 
run this entire set of benchmarks, call the main function of `RunBenchmarks.java`. The results of running the benchmarks are written
to the `Outputs` subdirectory.
