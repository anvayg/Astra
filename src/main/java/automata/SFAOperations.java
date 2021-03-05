package automata;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import automata.sfa.*;
import theory.BooleanAlgebra;
import theory.characters.CharPred;

/**
 * Class for functions/operations on SFA over characters
 * 
 * @author anvaygrover
 *
 */
public class SFAOperations {
	
	public static Integer getSuccessorState(SFA<CharPred, Character> aut, Integer state, Character move, 
			BooleanAlgebra<CharPred, Character> ba) throws TimeoutException {
		Collection<SFAMove<CharPred, Character>> transitions = aut.getTransitionsFrom(state);
		
		// assumes disjoint and total set of transitions (minterm reduced)
		for (SFAMove<CharPred, Character> transition : transitions) {
			if (transition.hasModel(move, ba)) {
				return transition.to;
			}
		}
		
		// should be unreachable if total
		return -1;
	}
	
	/*
	 * Similar to getSuccessorState but check whether transition is present
	 */
	public static boolean hasTransition(SFA<CharPred, Character> aut, Integer state, Character move, 
			BooleanAlgebra<CharPred, Character> ba) throws TimeoutException {
		Collection<SFAMove<CharPred, Character>> transitions = aut.getTransitionsFrom(state);
		
		// assumes disjoint and total set of transitions (minterm reduced)
		for (SFAMove<CharPred, Character> transition : transitions) {
			if (transition.hasModel(move, ba)) {
				return true;
			}
		}
		
		return false;
	}
	
	// Assume aut1 and aut2 have transitions labeled with single characters
	public static HashSet<Character> alphabetSet(SFA<CharPred, Character> aut1, SFA<CharPred, Character> aut2,
			BooleanAlgebra<CharPred, Character> ba) throws TimeoutException {
		HashSet<Character> alphabet = new HashSet<Character>();
		Collection<SFAMove<CharPred, Character>> transitions1 = aut1.getTransitions();
		Collection<SFAMove<CharPred, Character>> transitions2 = aut2.getTransitions();
		
		for (SFAMove<CharPred, Character> transition : transitions1) {
			Character label = transition.getWitness(ba);
			alphabet.add(label);
		}
		
		for (SFAMove<CharPred, Character> transition : transitions2) {
			Character label = transition.getWitness(ba);
			alphabet.add(label);
		}	
		
		alphabet.add(Character.MIN_VALUE); // use for empty
		return alphabet;
	}
	
	public static HashMap<Character, Integer> mkAlphabetMap(Set<Character> alphabet) {
		HashMap<Character, Integer> alphabetMap = new HashMap<Character, Integer>();
		int counter = 0;
		
		for (Character sym : alphabet) {
			alphabetMap.put(sym, counter);
			counter++;
		}
		
		return alphabetMap;
	}
	
	public static SFA<CharPred, Character> mkTotalFinite(SFA<CharPred, Character> aut, Collection<Character> alphabet, BooleanAlgebra<CharPred, Character> ba) throws TimeoutException {
		Collection<SFAMove<CharPred, Character>> transitions = new ArrayList<SFAMove<CharPred, Character>>();
		int sinkState = aut.getMaxStateId() + 1;
		transitions.addAll(aut.getTransitions());
		
		for (Integer state : aut.getStates()) {
			for (Character c : alphabet) {
				if (!hasTransition(aut, state, c, ba)) {
					transitions.add(new SFAInputMove<CharPred, Character>(state, sinkState, ba.MkAtom(c)));
				}
			}
		}
		
		// self-loop on sinkState
		for (Character c : alphabet) {
			transitions.add(new SFAInputMove<CharPred, Character>(sinkState, sinkState, ba.MkAtom(c)));
		}
		
		return SFA.MkSFA(transitions, aut.getInitialState(), aut.getFinalStates(), ba, false, false);
	}
	
	
}
