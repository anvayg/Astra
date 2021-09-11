package benchmarks;

import static org.junit.Assert.assertTrue;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
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
	
	public static void runBenchmark(String inputFilename, String benchmarkName, String outputFilename) throws Exception {
		File file = new File(inputFilename);
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
		
		if (outputFilename == null) {
			outputFilename = "src/test/java/benchmarks/Outputs/" + benchmarkName + "_out";
		} else {
			outputFilename = "src/test/java/benchmarks/Outputs/" + outputFilename;
		}
		// Open output file
		BufferedWriter br = new BufferedWriter(new FileWriter(new File(outputFilename), true));
		br.write(benchmarkName + "\n");
		
		// Call solver
		Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String> result = 
				Driver.runAlgorithm(source, target, numStates, outputBound, fraction, examples, null, "src/test/java/benchmarks/tmpOutput", benchmarkName);
	}
	
	
	/* Repairing from the input */
	public static Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String> 
	runRepairBenchmark(SFT<CharPred, CharFunc, Character> aut, SFA<CharPred, Character> source, SFA<CharPred, Character> target, 
			Collection<Pair<CharPred, ArrayList<Integer>>> minterms, int numStates, int outputBound, int[] fraction, 
			List<Pair<String, String>> examples, SFA<CharPred, Character> template, String benchmarkName, 
			String outputFilename) throws TimeoutException, IOException {

		if (outputFilename == null) {
			outputFilename = "src/test/java/benchmarks/RepairBenchmarks/" + benchmarkName + "_out";
		} else {
			outputFilename = "src/test/java/benchmarks/RepairBenchmarks/" + outputFilename;
		}
		BufferedWriter br = new BufferedWriter(new FileWriter(new File(outputFilename)));
		br.write("Running benchmark\n");
		br.close();
		
		if (source == null) {
			// Take the preimage
			SFA<CharPred, Character> preimage = aut.inverseImage(target, ba);
			source = aut.getDomain(ba).minus(preimage, ba).determinize(ba);
			
			// Restrict aut to 'good' subset of input (i.e. the preimage)
			aut = aut.domainRestriction(preimage, ba);
		}
			// else assume that aut is already restricted
		
		
		// Un-normalize source and target using minterms
		Pair<SFA<CharPred, Character>, SFA<CharPred, Character>> unnormalized = SFAOperations.unnormalize(source, target, minterms, ba);
		source = unnormalized.first;
		System.out.println(source.toDotString(ba));
		target = unnormalized.second;
		
		
		Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String> result = 
				Driver.runAlgorithm(source, target, numStates, outputBound, fraction, examples, null, outputFilename, benchmarkName);
		SFT<CharPred, CharFunc, Character> mySFT = result.first.first;
		SFT<CharPred, CharFunc, Character> mySFT2 = result.second.first;
		String witness = result.third;

		SFT<CharPred, CharFunc, Character> mySFTrepair = aut.unionWith(mySFT, ba);
		System.out.println(mySFTrepair.toDotString(ba));

		br = new BufferedWriter(new FileWriter(new File(outputFilename), true));
		br.write("SFTrepair1:\n");
		br.write(mySFTrepair.toDotString(ba));

		SFT<CharPred, CharFunc, Character> mySFT2repair = null;
		if (witness != null) {
			mySFT2repair = aut.unionWith(mySFT2, ba);
			br.write("SFTrepair2:\n");
			br.write(mySFT2repair.toDotString(ba));
		}
		br.close();

		Pair<SFT<CharPred, CharFunc, Character>, Long> pair1 = new Pair<SFT<CharPred, CharFunc, Character>, Long>(mySFTrepair, result.first.second);
		Pair<SFT<CharPred, CharFunc, Character>, Long> pair2 = new Pair<SFT<CharPred, CharFunc, Character>, Long>(mySFT2repair, result.second.second);
		return new Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String>(pair1, pair2, witness);
	}
	
	
	/* Repairing from the output language */
	public static Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String> 
	runRepairBenchmarkOutput(SFT<CharPred, CharFunc, Character> aut, SFA<CharPred, Character> source, SFA<CharPred, Character> target, 
			int numStates, int outputBound, int[] fraction, List<Pair<String, String>> examples, SFA<CharPred, Character> template, 
			String benchmarkName) throws TimeoutException, IOException {
		
		String filename = "src/test/java/benchmarks/RepairBenchmarks/" + benchmarkName + "_out";
		BufferedWriter br = new BufferedWriter(new FileWriter(new File(filename)));
		br.write("Running benchmark\n");
		br.close();
		Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String> result = 
				Driver.runAlgorithm(source, target, numStates, outputBound, fraction, examples, null, filename, benchmarkName);
		SFT<CharPred, CharFunc, Character> mySFT = result.first.first;
		SFT<CharPred, CharFunc, Character> mySFT2 = result.second.first;
		String witness = result.third;

		SFT<CharPred, CharFunc, Character> mySFTrepair = aut.composeWith(mySFT, ba);
		System.out.println(mySFTrepair.toDotString(ba));

		br = new BufferedWriter(new FileWriter(new File(filename), true));
		br.write("SFTrepair1:\n");
		br.write(mySFTrepair.toDotString(ba));

		SFT<CharPred, CharFunc, Character> mySFT2repair = null;
		if (witness != null) {
			mySFT2repair = aut.composeWith(mySFT2, ba);
			br.write("SFTrepair2:\n");
			br.write(mySFT2repair.toDotString(ba));
		}
		br.close();

		Pair<SFT<CharPred, CharFunc, Character>, Long> pair1 = new Pair<SFT<CharPred, CharFunc, Character>, Long>(mySFTrepair, result.first.second);
		Pair<SFT<CharPred, CharFunc, Character>, Long> pair2 = new Pair<SFT<CharPred, CharFunc, Character>, Long>(mySFT2repair, result.second.second);
		return new Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String>(pair1, pair2, witness);
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
		    	runBenchmark("src/test/java/benchmarks/Benchmarks/" + file.getName(), file.getName(), null);
		    	// if (counter == 3) break;
		    	counter++;
		    }
		    
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
