package benchmarks;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import org.sat4j.specs.TimeoutException;

import automata.sfa.SFA;
import solver.Driver;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import utilities.Pair;
import utilities.SFAprovider;
import utilities.Triple;

public class RunRegexBenchmarks {
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	// Merge this with RunBenchmarks later
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
		source.minimize(ba);
		SFA<CharPred, Character> target = (new SFAprovider(targetRegex, ba)).getSFA().removeEpsilonMoves(ba);
		if (!target.isDeterministic(ba)) target = target.determinize(ba);
		target.minimize(ba);
		
		if (outputFilename == null) {
			outputFilename = "src/test/java/benchmarks/RegexBenchOutputs/" + benchmarkName + "_out";
		} else {
			outputFilename = "src/test/java/benchmarks/RegexBenchOutputs/" + outputFilename;
		}
		// Open output file
		BufferedWriter br = new BufferedWriter(new FileWriter(new File(outputFilename)));
		br.write(benchmarkName + "\n");
		br.close();
		
		// Call solver
		Triple<Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, String> result = 
				Driver.runAlgorithm(source, target, numStates, outputBound, 0, fraction, examples, null, null, null, null, outputFilename, benchmarkName);
	}
	
	public static void main(String[] args) throws TimeoutException {
		try {
			// Benchmarks directory
			File directoryPath = new File("src/test/java/benchmarks/RegexBenchmarks");

			// List of all benchmarks
			File filesList[] = directoryPath.listFiles();

			for(File file : filesList) {
				runBenchmark("src/test/java/benchmarks/RegexBenchmarks/" + file.getName(), file.getName(), null);
			}

		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
