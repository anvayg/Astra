package automata.fst;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.tuple.ImmutablePair;
import org.sat4j.specs.TimeoutException;

import automata.SFAOperations;
import theory.BooleanAlgebraSubst;
import theory.characters.CharConstant;
import theory.characters.CharFunc;
import theory.characters.CharOffset;
import theory.characters.CharPred;
import transducers.sft.SFT;
import transducers.sft.SFTInputMove;
import transducers.sft.SFTMove;
import utilities.Pair;

public class FSTOperations {
	
	/* Minterm-exapnsion of character-character FST */
	public static SFT<CharPred, CharFunc, Character> mintermExpansion(FST<Character, Character> aut,
			Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterm, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) throws TimeoutException {
		Collection<SFTMove<CharPred, CharFunc, Character>> newTransitions = new ArrayList<SFTMove<CharPred, CharFunc, Character>>();
		
		for (Integer state : aut.getStates()) {
			for (FSTMove<Character, Character> transition : aut.getTransitionsFrom(state)) {
				Character c = transition.input;
				CharPred pred = idToMinterm.get(new CharPred(c)).first;
				
				/* build outputFunc */
				List<CharFunc> output = new ArrayList<CharFunc>();
				for (Character f: transition.outputs) { 		
					if (c.equals(f)) {
						output.add(CharOffset.IDENTITY); // identity if input/output minterms are the same
					} else {
						CharPred inputMinterm = SFAOperations.findSatisfyingMinterm(c, idToMinterm).first;
						CharPred outputMinterm = SFAOperations.findSatisfyingMinterm(f, idToMinterm).first;

						if (inputMinterm.intervals.size() == 1 && outputMinterm.intervals.size() == 1) {
							ImmutablePair<Character, Character> inputInterval = inputMinterm.intervals.get(0);
							ImmutablePair<Character, Character> outputInterval = outputMinterm.intervals.get(0);

							int inputIntervalSize = inputInterval.right - inputInterval.left;
							int outputIntervalSize = outputInterval.right - outputInterval.left;

							if (inputIntervalSize == outputIntervalSize) {
								int offset = outputInterval.left - inputInterval.left;
								output.add(new CharOffset(offset));
							} else {
								output.add(new CharConstant(f));
							}
						} else {
							output.add(new CharConstant(f));
						}
					}
				}
				
				SFTInputMove<CharPred, CharFunc, Character> newTransition = new SFTInputMove<CharPred, CharFunc, Character>(transition.from, transition.to, pred, output);
				newTransitions.add(newTransition);
			}
		}
		
		HashMap<Integer, Set<List<Character>>> finStates = new HashMap<Integer, Set<List<Character>>>();
		for (Integer finState : aut.getFinalStates()) {
			Set<List<Character>> emptyTail = new HashSet<List<Character>>();
			finStates.put(finState, emptyTail);
		}
		
		return SFT.MkSFT(newTransitions, aut.getInitialState(), finStates, ba);
	}
	
	/* TODO minterm exapnsion of lookahead FST */
	public static SFT<CharPred, CharFunc, Character> mintermExpansion(FSTLookahead<Character, Character> aut,
			Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterm, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) throws TimeoutException {
		FST<Pair<Character, Integer>, Character> fst = aut.fst;
		
		
		return null;
	}
	
	
}
