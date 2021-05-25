package solver;

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
			SFT<CharPred, CharFunc, Character> mySFT = c.mkConstraints(numStates, outputLength, fraction, examplesFinite, null, null, false);
			
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

}
