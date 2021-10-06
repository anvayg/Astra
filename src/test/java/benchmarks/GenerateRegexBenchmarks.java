package benchmarks;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import SFT.GetTag;
import automata.RegexFSA;
import automata.sfa.SFA;
import theory.characters.CharConstant;
import theory.characters.CharFunc;
import theory.characters.CharOffset;
import theory.characters.CharPred;
import theory.characters.StdCharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import transducers.sft.SFTInputMove;
import transducers.sft.SFTMove;
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
	
	public static void generateGetTags(String outputFilename, String outputDirectory, String printMode) throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> GetTags = GetTag.MkGetTagsSFT();
		
		SFA<CharPred, Character> source = GetTags.getDomain(ba).removeEpsilonMoves(ba).determinize(ba);
		SFA<CharPred, Character> target = GetTags.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		
		RegexFSA sourceRegexFSA = new RegexFSA(source);
		String sourceRegex = sourceRegexFSA.toRegex(printMode);
		
		RegexFSA targetRegexFSA = new RegexFSA(target);
		String targetRegex = targetRegexFSA.toRegex(printMode);
		
		if (outputFilename == null) {
			outputFilename = outputDirectory + "getTags";
		} else {
			outputFilename = outputDirectory + outputFilename;
		}
		
		// Write benchmark
		BufferedWriter br = new BufferedWriter(new FileWriter(new File(outputFilename)));
		br.write(sourceRegex + "\n");
		br.write(targetRegex + "\n");
		br.close();
	}
	
	public static SFT<CharPred, CharFunc, Character> mkEscapeQuotes() throws TimeoutException {
		CharPred quotes = ba.MkOr(new CharPred('\''), new CharPred('\"'));
		CharPred backslash = new CharPred('\\');
		
		List<SFTMove<CharPred, CharFunc, Character>> transitions17 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output171 = new ArrayList<CharFunc>();
		output171.add(CharOffset.IDENTITY);
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, StdCharPred.ALPHA_NUM, output171));
		List<CharFunc> output172 = new ArrayList<CharFunc>();
		output172.add(new CharConstant('\\'));
		output172.add(CharOffset.IDENTITY);
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, quotes, output172));
		List<CharFunc> output173 = new ArrayList<CharFunc>();
		output173.add(CharOffset.IDENTITY); // corrected
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, backslash, output173));
		List<CharFunc> output174 = new ArrayList<CharFunc>();
		output174.add(CharOffset.IDENTITY);
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, backslash, output174)); // corrected
		List<CharFunc> output175 = new ArrayList<CharFunc>();
		output175.add(CharOffset.IDENTITY);
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, ba.MkOr(quotes, StdCharPred.ALPHA_NUM), output175));
		Map<Integer, Set<List<Character>>> finStatesAndTails17 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails17.put(0, new HashSet<List<Character>>());
		finStatesAndTails17.put(1, new HashSet<List<Character>>());
		return SFT.MkSFT(transitions17, 0, finStatesAndTails17, ba);
	}
	
	public static void generateEscapeQuotes(String outputFilename, String outputDirectory, String printMode) throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> EscapeQuotes = mkEscapeQuotes();
		System.out.println(EscapeQuotes.toDotString(ba));
		
		SFA<CharPred, Character> source = EscapeQuotes.getDomain(ba);
		System.out.println(source.toDotString(ba));
		
		SFA<CharPred, Character> target = EscapeQuotes.getOverapproxOutputSFA(ba).determinize(ba);
		System.out.println(target.toDotString(ba));
		
		RegexFSA sourceRegexFSA = new RegexFSA(source);
		String sourceRegex = sourceRegexFSA.toRegex(printMode);
		
		RegexFSA targetRegexFSA = new RegexFSA(target);
		String targetRegex = targetRegexFSA.toRegex(printMode);
		
		if (outputFilename == null) {
			outputFilename = outputDirectory + "escapeQuotes";
		} else {
			outputFilename = outputDirectory + outputFilename;
		}
		
		// Write benchmark
		BufferedWriter br = new BufferedWriter(new FileWriter(new File(outputFilename)));
		br.write(sourceRegex + "\n");
		br.write(targetRegex + "\n");
		br.close();
	}
	
	public static void generateFiniteEscapeQuotes(String outputFilename, String outputDirectory, String printMode) throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> EscapeQuotes = SFTSynthBench.mkFiniteEscapeQuotes();
		System.out.println(EscapeQuotes.toDotString(ba));
		
		SFA<CharPred, Character> source = EscapeQuotes.getDomain(ba);
		System.out.println(source.toDotString(ba));
		
		SFA<CharPred, Character> target = EscapeQuotes.getOverapproxOutputSFA(ba).determinize(ba);
		System.out.println(target.toDotString(ba));
		
		RegexFSA sourceRegexFSA = new RegexFSA(source);
		String sourceRegex = sourceRegexFSA.toRegex(printMode);
		
		RegexFSA targetRegexFSA = new RegexFSA(target);
		String targetRegex = targetRegexFSA.toRegex(printMode);
		
		if (outputFilename == null) {
			outputFilename = outputDirectory + "finiteEscapeQuotes";
		} else {
			outputFilename = outputDirectory + outputFilename;
		}
		
		// Write benchmark
		BufferedWriter br = new BufferedWriter(new FileWriter(new File(outputFilename)));
		br.write(sourceRegex + "\n");
		br.write(targetRegex + "\n");
		br.close();
	}
	
	public static void main(String[] args) throws TimeoutException {
		try {
			// Benchmarks directory
			File directoryPath = new File("src/test/java/benchmarks/Benchmarks");
		    
			// List of all benchmarks
		    File filesList[] = directoryPath.listFiles();
			
		    for (File file : filesList) {
		    	generateRegexBenchmark("src/test/java/benchmarks/Benchmarks/" + file.getName(), file.getName(), null, "src/test/java/benchmarks/RegexBenchmarksLenses/", "lenses");
		    }
		    
		    for (File file : filesList) {
		    	generateRegexBenchmark("src/test/java/benchmarks/Benchmarks/" + file.getName(), file.getName(), null, "src/test/java/benchmarks/RegexBenchmarks/", null);
		    }
		    
		    directoryPath = new File("src/test/java/benchmarks/Benchmarks2");
		    File filesList2[] = directoryPath.listFiles();
		    
		    for (File file : filesList2) {
		    	generateRegexBenchmark("src/test/java/benchmarks/Benchmarks2/" + file.getName(), file.getName(), null, "src/test/java/benchmarks/RegexBenchmarksLenses/", "lenses");
		    }
		    
		    // getTags
		    generateGetTags(null, "src/test/java/benchmarks/RegexBenchmarksLenses/", "lenses");
		    
		    // escapeQuotes
		    generateEscapeQuotes(null, "src/test/java/benchmarks/RegexBenchmarksLenses/", "lenses");
		    
		    // finiteEscapeQuotes
		    generateFiniteEscapeQuotes(null, "src/test/java/benchmarks/RegexBenchmarksLenses/", "lenses");
		    
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
