package solver;

import static org.junit.Assert.assertTrue;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.Context;

import automata.SFAOperations;
import automata.SFTOperations;
import automata.sfa.SFA;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import utilities.Pair;
import utilities.Triple;

public class Driver {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	/* Convert example strings to their 'finite' versions using minterms (this is duplicated) */
	static List<Pair<String, String>> finitizeExamples(List<Pair<String, String>> ioExamples, 
			Map<CharPred, Pair<CharPred, ArrayList<Integer>>> minterms) throws TimeoutException {
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		
		for (Pair<String, String> example : ioExamples) {
			String input = SFAOperations.finitizeStringMinterms(example.first, minterms, ba);
			String output = SFAOperations.finitizeStringMinterms(example.second, minterms, ba);
			examples.add(new Pair<String, String>(input, output));
		}
		
		return examples;
	}
	
	/* Basic version of algorithm, currently without templates */
	public static SFT<CharPred, CharFunc, Character> runBasicAlgorithm(SFA<CharPred, Character> source, SFA<CharPred, Character> target, 
			List<Pair<String, String>> examples) throws TimeoutException {
		/* Going with fractional permitted cost of 1/1 */
		int[] fraction = new int[] {1, 1};
		
		/* Start with single state */
		int numStates = 1;
		
		/* Start with output length = 1*/
		int outputLength = 1;
		
		HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
		
		// Make finite automata out of source and target
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(source, target, ba);
		
		SFA<CharPred, Character> sourceFinite = triple.first;
		SFA<CharPred, Character> targetFinite = triple.second;
		
		Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterm = triple.third;
		
		List<Pair<String, String>> examplesFinite = finitizeExamples(examples, idToMinterm);
		
		Set<Character> sourceAlphabetSet = SFAOperations.alphabetSet(sourceFinite, ba);
		Set<Character> targetAlphabetSet = SFAOperations.alphabetSet(targetFinite, ba);
		Set<Character> alphabetSet = new HashSet<Character>();
		alphabetSet.addAll(sourceAlphabetSet);
		alphabetSet.addAll(targetAlphabetSet);
		
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		
		// Make target FA total
		SFA<CharPred, Character> targetTotal = SFAOperations.mkTotalFinite(targetFinite, alphabetSet, ba);
		
		ConstraintsBV c = new ConstraintsBV(ctx, sourceFinite, targetTotal, alphabetMap, ba);
		
		while (true) {
			/* Call solver */
			SFT<CharPred, CharFunc, Character> mySFT = c.mkConstraints(numStates, outputLength, fraction, examplesFinite, null, null, null, false).first;
			
			if (mySFT.getTransitions().size() == 0) { // if UNSAT
				if (numStates < sourceFinite.stateCount()) {
					numStates++;
				} else if (outputLength < 4) { 	// too much?
					outputLength++;
				} else {
					return null;
				}
			} else {
				return SFTOperations.mintermExpansion(mySFT, triple.third, ba);
			}
		}
	}

	
	public static Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String> 
	runAlgorithm(SFA<CharPred, Character> source, SFA<CharPred, Character> target, 
			int numStates, int outputBound, int[] fraction, List<Pair<String, String>> examples, 
			SFA<CharPred, Character> template, String filename, String benchmarkName) throws TimeoutException, IOException {
		HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
		
		// Make finite automata out of source and target
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(source, target, ba);
		
		SFA<CharPred, Character> sourceFinite = triple.first;
		SFA<CharPred, Character> targetFinite = triple.second;
		
		Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterm = triple.third;
		
		List<Pair<String, String>> examplesFinite = finitizeExamples(examples, idToMinterm);
		
		Set<Character> sourceAlphabetSet = SFAOperations.alphabetSet(sourceFinite, ba);
		Set<Character> targetAlphabetSet = SFAOperations.alphabetSet(targetFinite, ba);
		Set<Character> alphabetSet = new HashSet<Character>();
		alphabetSet.addAll(sourceAlphabetSet);
		alphabetSet.addAll(targetAlphabetSet);
		
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		
		// Make target FA total
		SFA<CharPred, Character> targetTotal = SFAOperations.mkTotalFinite(targetFinite, alphabetSet, ba);
		
		// Variables to be set later
		SFT<CharPred, CharFunc, Character> mySFT = null;
		SFT<CharPred, CharFunc, Character> mySFT2 = null;
		String witness = null;
		long solvingTime1 = 0;
		long solvingTime2 = 0;
		
		long startTime = System.nanoTime();
		ConstraintsSolver c = new ConstraintsSolver(ctx, sourceFinite, targetTotal, alphabetMap, numStates, outputBound, examplesFinite, "mean", fraction, template, null, null, ba);
		Pair<SFT<CharPred, CharFunc, Character>, Long> res = c.mkConstraints(null, false);
		mySFT = res.first;
		solvingTime1 = res.second;
	
		long stopTime = System.nanoTime();
		long time1 = (stopTime - startTime) / 1000000;
		
		if (mySFT.getTransitions().size() != 0) { // if SAT
			// Get second solution, if there is one
			startTime = System.nanoTime();
			c = new ConstraintsSolver(ctx, sourceFinite, targetTotal, alphabetMap, numStates, outputBound, examplesFinite, "mean", fraction, null, mySFT, null, ba);
			res = c.mkConstraints(null, false);
			stopTime = System.nanoTime();
			mySFT2 = res.first;
			solvingTime2 = res.second;
		}
		long time2 = (stopTime - startTime) / 1000000;
		
		// Call minterm expansion
		SFT<CharPred, CharFunc, Character> mySFTexpanded = SFTOperations.mintermExpansion(mySFT, triple.third, ba);
		SFT<CharPred, CharFunc, Character> mySFTrestricted = SFTOperations.mkAllStatesFinal(mySFTexpanded, ba).domainRestriction(source, ba);
		
		SFT<CharPred, CharFunc, Character> mySFT2expanded = null;
		SFT<CharPred, CharFunc, Character> mySFT2restricted = null;
		if (mySFT2 != null) {
			mySFT2expanded = SFTOperations.mintermExpansion(mySFT2, triple.third, ba);
			mySFT2restricted = SFTOperations.mkAllStatesFinal(mySFT2expanded, ba).domainRestriction(source, ba);
		}
		
		if (mySFT2restricted != null) {
			System.out.println(mySFTexpanded.toDotString(ba));
			System.out.println(mySFTrestricted.toDotString(ba));
			System.out.println(mySFT2restricted.toDotString(ba));
			// Check equality of expanded transducers
			if (!SFT.decide1equality(mySFTrestricted, mySFT2restricted, ba)) {
				System.out.println("Not equiv");
				try {
					List<Character> witnessChars = SFT.witness1disequality(mySFTrestricted, mySFT2restricted, ba);
					StringBuilder sb = new StringBuilder();
					for (Character ch : witnessChars) {
						sb.append(ch);
					}
					witness = sb.toString();
				} catch(Exception e) {
					// TODO
				}
			}
		}
		
		// If stats are needed, write to filename
		if (filename != null) {
			BufferedWriter br = new BufferedWriter(new FileWriter(new File(filename), true));
			
			if (benchmarkName != null) {
				br.write(benchmarkName + " statistics:\n");
			}
			
			br.write("States in source: " + source.stateCount() + "\n");
			br.write("States in target: " + target.stateCount() + "\n");
			br.write("Transitions in source: " + source.getTransitionCount() + "\n");
			br.write("Transitions in target: " + target.getTransitionCount() + "\n");
			br.write("Transitions in sourceFinite: " + sourceFinite.getTransitionCount() + "\n");
			br.write("Transitions in targetFinite: " + targetFinite.getTransitionCount() + "\n");
			br.write("Size of alphabet: " + alphabetMap.size() + "\n");
			br.write("Number of examples: " + examples.size() + "\n");
			br.write("SFT1 solving time: " + solvingTime1 + "\n");
			if (mySFT2restricted != null) {
				br.write("SFT2 solving time: " + solvingTime2 + "\n");
			}
			
			for (Pair<String, String> example : examples) {
	        	String exampleOutput = SFTOperations.getOutputString(mySFTrestricted, example.first, ba);
	        	try {
	        		assertTrue(exampleOutput.equals(example.second));
	        	} catch (AssertionError error) {
	        		// TODO: Error collector
	        		br.write("Assertion failed: " + exampleOutput + ", " + example.second + "\n");
	        	}
	        }
			
			if (mySFTrestricted.getTransitions().size() != 0) {
				br.write("First SFT:\n");
				br.write(mySFTrestricted.toDotString(ba) + "\n");
				br.write("Synthesis time: " + time1 + "\n");
			} else {
				br.write("UNSAT\n");
			}
			
			if (witness != null) {
				br.write("Second SFT:\n");
				br.write(mySFT2restricted.toDotString(ba) + "\n");
				br.write("Synthesis time: " + time2 + "\n");

				String witnessOutput1 = SFTOperations.getOutputString(mySFTrestricted, witness, ba);
				String witnessOutput2 = SFTOperations.getOutputString(mySFT2restricted, witness, ba);

				br.write("Input on which SFTs differ: " + witness + "\n");
				br.write("Output1: " + witnessOutput1 + "\n");
				br.write("Output2: " + witnessOutput2 + "\n");
			} else {
				if (mySFT2restricted != null) br.write("Equivalent results");
				else br.write("No other solution\n");
			}
			
			br.write("\n\n");
			br.close();
		}
		
		Pair<SFT<CharPred, CharFunc, Character>, Long> pair1 = new Pair<SFT<CharPred, CharFunc, Character>, Long>(mySFTrestricted, time1);
		Pair<SFT<CharPred, CharFunc, Character>, Long> pair2 = new Pair<SFT<CharPred, CharFunc, Character>, Long>(mySFT2restricted, time2);
		return new Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String>(pair1, pair2, witness);
	}
}

