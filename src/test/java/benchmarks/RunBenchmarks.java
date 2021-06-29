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
import utilities.Triple;

public class RunBenchmarks {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	public static void runBenchmarkBasic(String filename) throws Exception {
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
			if (input.equals("")) break;
			String output = sc.nextLine();
			
			examples.add(new Pair<String, String>(input, output));
		}
		System.out.println(examples);
		
		SFA<CharPred, Character> source = (new SFAprovider(sourceRegex, ba)).getSFA().removeEpsilonMoves(ba);
		SFA<CharPred, Character> target = (new SFAprovider(targetRegex, ba)).getSFA().removeEpsilonMoves(ba);
		
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
	
	public static void runBenchmark(String filename, String benchmarkName) throws Exception {
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
			if (input.equals("")) break;
			String output = sc.nextLine();
			
			examples.add(new Pair<String, String>(input, output));
		}
		System.out.println(examples);
		
		// Order of specification: states, output_length, edit-distance
		int numStates = Integer.parseInt(sc.nextLine());
		
		int outputBound = Integer.parseInt(sc.nextLine());
		
		String editDistString = sc.nextLine();
		String[] editDistArray = editDistString.split("/");		// length = 2
		if (editDistArray.length != 2) throw new IllegalArgumentException("Incorrect edit-distance format");
		
		int[] fraction = new int[2];
		for (int i = 0; i < editDistArray.length; i++) {
			fraction[i] = Integer.parseInt(editDistArray[i]);
		}
		
		SFA<CharPred, Character> source = (new SFAprovider(sourceRegex, ba)).getSFA().removeEpsilonMoves(ba);
		if (!source.isDeterministic(ba)) source = source.determinize(ba);
		SFA<CharPred, Character> target = (new SFAprovider(targetRegex, ba)).getSFA().removeEpsilonMoves(ba);
		if (!target.isDeterministic(ba)) target = target.determinize(ba);
		
		Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String> result = Driver.runAlgorithm(source, target, numStates, outputBound, fraction, examples, null);
		SFT<CharPred, CharFunc, Character> mySFT = result.first.first;
		SFT<CharPred, CharFunc, Character> mySFT2 = result.second.first;
		String witness = result.third;
		
		long time1 = result.first.second / 1000000;
		long time2 = result.second.second / 1000000;
		
		System.out.println(mySFT.toDotString(ba));
		
		BufferedWriter br = new BufferedWriter(new FileWriter(new File("src/test/java/benchmarks/tmpOutput"), true));
		br.write(benchmarkName + "\n");
		for (Pair<String, String> example : examples) {
        	String exampleOutput = SFTOperations.getOutputString(mySFT, example.first, ba);
        	try {
        		assertTrue(exampleOutput.equals(example.second));
        	} catch (AssertionError error) {
        		// TODO: Error collector
        		br.write("Assertion failed: " + exampleOutput + ", " + example.second + "\n");
        	}
        }
		
		if (mySFT.getTransitions().size() != 0) {
			br.write("First SFT:\n");
			br.write(mySFT.toDotString(ba) + "\n");
			br.write("Synthesis time: " + time1 + "\n");
		} else {
			br.write("UNSAT\n");
		}
		
		if (witness != null) {
			br.write("Second SFT:\n");
			br.write(mySFT2.toDotString(ba) + "\n");
			br.write("Synthesis time: " + time2 + "\n");

			String witnessOutput1 = SFTOperations.getOutputString(mySFT, witness, ba);
			String witnessOutput2 = SFTOperations.getOutputString(mySFT2, witness, ba);

			br.write("Input on which SFTs differ: " + witness + "\n");
			br.write("Output1: " + witnessOutput1 + "\n");
			br.write("Output2: " + witnessOutput2 + "\n");
		} else {
			if (mySFT2 != null) br.write("Equivalent results");
			else br.write("No other solution\n");
		}
		
		br.write("\n\n");
		br.close();
	}

	public static void main(String[] args) throws TimeoutException {
		try {
			// Benchmarks directory
			File directoryPath = new File("src/test/java/benchmarks/Benchmarks");
		      
			// List of all benchmarks
		    File filesList[] = directoryPath.listFiles();
		    
		    // Reset output file
		    BufferedWriter br = new BufferedWriter(new FileWriter(new File("src/test/java/benchmarks/tmpOutput")));
		    br.write("Starting experiments\n");
		    br.close();
			
		    int counter = 0;
		    for(File file : filesList) {
		    	runBenchmark("src/test/java/benchmarks/Benchmarks/" + file.getName(), file.getName());
		    	// if (counter == 3) break;
		    	counter++;
		    }
		    
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
