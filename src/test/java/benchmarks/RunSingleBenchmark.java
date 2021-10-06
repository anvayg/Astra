package benchmarks;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;

public class RunSingleBenchmark {

	public static void main(String[] args) {
		try {
			// Benchmarks directory
			String directoryPath = args[0];
		      
			// Benchmark to run
		    String benchmark = args[1];
			
		    RunBenchmarks.runBenchmark(directoryPath + benchmark, benchmark, null);
		    
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
