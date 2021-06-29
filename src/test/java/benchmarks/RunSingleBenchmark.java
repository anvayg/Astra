package benchmarks;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;

public class RunSingleBenchmark {

	public static void main(String[] args) {
		try {
			// Benchmarks directory
			File directoryPath = new File("src/test/java/benchmarks/Benchmarks/");
		      
			// Benchmark to run
		    String benchmark = args[0];
		    
		    // Reset output file
		    BufferedWriter br = new BufferedWriter(new FileWriter(new File("src/test/java/benchmarks/tmpOutput")));
		    br.write("Running benchmark\n");
		    br.close();
			
		    RunBenchmarks.runBenchmark("src/test/java/benchmarks/Benchmarks/" + benchmark, benchmark);
		    
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
