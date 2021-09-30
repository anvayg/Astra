package benchmarks;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import org.sat4j.specs.TimeoutException;

import automata.RegexFSA;
import automata.sfa.SFA;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import utilities.Pair;
import utilities.SFAprovider;

public class GenerateRegexBenchmarks {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	public static void generateRegexBenchmark(String inputFilename, String benchmarkName, String outputFilename, 
			String outputDirectory, String printMode) throws TimeoutException, IOException {
		File file = new File(inputFilename);
		Scanner sc = null;
		try {
			sc = new Scanner(file);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		
		String sourceRegex = sc.nextLine();
		
		String targetRegex = sc.nextLine();
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		while (sc.hasNextLine()) {
			String input = sc.nextLine();
			if (input.equals("")) break;
			String output = sc.nextLine();
			
			examples.add(new Pair<String, String>(input, output));
		}
		
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
		
		// Re-convert to regex
		RegexFSA sourceRegexFSA = new RegexFSA(source);
		try {
			sourceRegex = sourceRegexFSA.toRegex(printMode);
		} catch (Error e) {
			System.out.println(benchmarkName);
			System.out.println(e.toString());
		}
		
		RegexFSA targetRegexFSA = new RegexFSA(target);
		targetRegex = targetRegexFSA.toRegex(printMode);
		
		if (outputFilename == null) {
			outputFilename = outputDirectory + benchmarkName;
		} else {
			outputFilename = outputDirectory + outputFilename;
		}
		
		// Write benchmark
		BufferedWriter br = new BufferedWriter(new FileWriter(new File(outputFilename)));
		br.write(sourceRegex + "\n");
		br.write(targetRegex + "\n");
		
		for (Pair<String, String> example : examples) {
			br.write(example.first + "\n");
			br.write(example.second + "\n");
		}
		
		br.write("\n");
		br.write(numStates + "\n");
		br.write(outputBound + "\n");
		br.write(fraction[0] + "/" + fraction[1]);
		br.close();
	}
	
	public static void main(String[] args) throws TimeoutException {
		try {
			// Benchmarks directory
			File directoryPath = new File("src/test/java/benchmarks/Benchmarks");
		    
			// List of all benchmarks
		    File filesList[] = directoryPath.listFiles();
			
		    for(File file : filesList) {
		    	generateRegexBenchmark("src/test/java/benchmarks/Benchmarks/" + file.getName(), file.getName(), null, "src/test/java/benchmarks/RegexBenchmarksLenses/", "lenses");
		    }
		    
		    for(File file : filesList) {
		    	generateRegexBenchmark("src/test/java/benchmarks/Benchmarks/" + file.getName(), file.getName(), null, "src/test/java/benchmarks/RegexBenchmarks/", null);
		    }
		    
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
