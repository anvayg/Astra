package benchmarks;

import static org.junit.Assert.assertTrue;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import org.sat4j.specs.TimeoutException;

import automata.SFAOperations;
import automata.SFTOperations;
import automata.sfa.SFA;
import solver.Driver;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import utilities.Pair;
import utilities.SFAprovider;

public class RunBenchmarks {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	public static void runBenchmark(SFA<CharPred, Character> source, SFA<CharPred, Character> target, 
			List<Pair<String, String>> examples) throws Exception {
		SFT<CharPred, CharFunc, Character> mySFT = Driver.runBasicAlgorithm(source, target, examples);
		System.out.println(mySFT.toDotString(ba));
		
		BufferedWriter br = new BufferedWriter(new FileWriter(new File("src/test/java/benchmarks/tmpOutput")));
		for (Pair<String, String> example : examples) {
        	String exampleOutput = SFTOperations.getOutputString(mySFT, example.first, ba);
        	try {
        		assertTrue(exampleOutput.equals(example.second));
        	} catch (AssertionError error) {
        		// TODO: Error collector
        		br.write("Assertion failed\n");
        	}
        }
		
		br.write(mySFT.toDotString(ba));
		br.close();
	}
	
	public static void readBenchmark(String filename) throws Exception {
		File file = new File(filename);
		Scanner sc = null;
		try {
			sc = new Scanner(file);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		
		String sourceRegex = sc.nextLine();
		System.out.println(sourceRegex);
		
		String targetRegex = sc.nextLine();
		System.out.println(targetRegex);
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		while (sc.hasNextLine()) {
			String input = sc.nextLine();
			String output = sc.nextLine();
			
			examples.add(new Pair<String, String>(input, output));
		}
		System.out.println(examples);
		
		SFA<CharPred, Character> source = (new SFAprovider(sourceRegex, ba)).getSFA().removeEpsilonMoves(ba);
		SFA<CharPred, Character> target = (new SFAprovider(targetRegex, ba)).getSFA().removeEpsilonMoves(ba);
		runBenchmark(source, target, examples);
	}

	public static void main(String[] args) throws TimeoutException {
		try {
			// Benchmarks directory
			File directoryPath = new File("src/test/java/benchmarks/LensBenchmarks");
		      
			// List of all benchmarks
		    File filesList[] = directoryPath.listFiles();
			
		    for(File file : filesList) {
		    	readBenchmark("src/test/java/benchmarks/LensBenchmarks/" + file.getName());
		    }
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
