package automata;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.tuple.ImmutablePair;
import org.sat4j.specs.TimeoutException;

import automata.sfa.SFA;
import automata.sfa.SFAEpsilon;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;
import theory.BooleanAlgebra;
import theory.BooleanAlgebraSubst;
import theory.characters.CharConstant;
import theory.characters.CharFunc;
import theory.characters.CharOffset;
import theory.characters.CharPred;
import transducers.sft.*;
import utilities.Pair;

public class SFTOperations {
	
	/* 
	 * Returns output string given a transducer and an input string. Assumes the alphabet of
	 * trans includes the character in inputStr. This function is meant for a finite 
	 * transducer, i.e., where the output functions are constants.
	 */
	public static String getOutputString(SFT<CharPred, CharFunc, Character> trans, String inputStr, 
			BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) throws TimeoutException {
		StringBuilder outputStr = new StringBuilder("");
		Integer state = trans.getInitialState();
		
		for (int i = 0; i < inputStr.length(); i++) {
			Character next = inputStr.charAt(i);
			Collection<SFTInputMove<CharPred, CharFunc, Character>> transitions = trans.getInputMovesFrom(state);
			
			for (SFTInputMove<CharPred, CharFunc, Character> transition : transitions) {
				if (transition.guard.isSatisfiedBy(next)) { 	// only 1 transition should be sat
					for (CharFunc f: transition.outputFunctions) {
						if (f != null) {
							Character out = ba.MkSubstFuncConst(f, next);
							outputStr.append(out);
							// System.out.println(next + ", " + out);
						}
					}
					state = transition.to;
				}
			}
		}
		
		return outputStr.toString();
	}
	
	public static Collection<Pair<CharPred, ArrayList<Integer>>> getMinterms(SFT<CharPred, CharFunc, Character> aut, 
			BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) {
		// Get all predicates
		ArrayList<CharPred> predicates = new ArrayList<CharPred>(); 

		for (Integer state : aut.getStates()) {
			for (SFTInputMove<CharPred, CharFunc, Character> transition : aut.getInputMovesFrom(state)) {
				predicates.add(transition.guard);
			}
		}
		
		// Get minterms
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = ba.GetMinterms(predicates);
		
		return minterms;
	}
	
	/* Performs minterm expansion */
	public static SFT<CharPred, CharFunc, Character> mintermExpansion(SFT<CharPred, CharFunc, Character> trans,
			Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterm, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) throws TimeoutException {
		Collection<SFTMove<CharPred, CharFunc, Character>> newTransitions = new ArrayList<SFTMove<CharPred, CharFunc, Character>>();
		
		for (Integer state : trans.getStates()) {
			for (SFTInputMove<CharPred, CharFunc, Character> transition : trans.getInputMovesFrom(state)) {
				SFTInputMove<CharPred, CharFunc, Character> newTransition = (SFTInputMove<CharPred, CharFunc, Character>) transition.clone();
				CharPred pred = idToMinterm.get(newTransition.guard).first;
				
				/* set new guard */
				newTransition.guard = pred;
				
				/* build new outputFunc */
				Character c = transition.getWitness(ba);
				
				List<CharFunc> output = new ArrayList<CharFunc>();
				for (CharFunc f: transition.outputFunctions) { 		
					if (f != null && f instanceof CharConstant) { 	// all the CharFuncs should be constants
							Character out = ((CharConstant)f).c;
							if (c.equals(out)) {
								output.add(CharOffset.IDENTITY); // identity if input/output minterms are the same
							} else {
								CharPred inputMinterm = SFAOperations.findSatisfyingMinterm(c, idToMinterm);
								CharPred outputMinterm = SFAOperations.findSatisfyingMinterm(out, idToMinterm);
								
								if (inputMinterm.intervals.size() == 1 && outputMinterm.intervals.size() == 1) {
									ImmutablePair<Character, Character> inputInterval = inputMinterm.intervals.get(0);
									ImmutablePair<Character, Character> outputInterval = outputMinterm.intervals.get(0);
									
									int inputIntervalSize = inputInterval.right - inputInterval.left;
									int outputIntervalSize = outputInterval.right - outputInterval.left;
									
									if (inputIntervalSize == outputIntervalSize) {
										int offset = outputInterval.left - inputInterval.left;
										output.add(new CharOffset(offset));
									} else {
										output.add(f);
									}
								} else {
									output.add(f);
								}
							}
					}
				}
				
				newTransition.outputFunctions = output;
				newTransitions.add(newTransition);
			}
		}
		
		return SFT.MkSFT(newTransitions, trans.getInitialState(), trans.getFinalStatesAndTails(), ba);
	}
	
	
	/* Makes all states final */
	public static SFT<CharPred, CharFunc, Character> mkAllStatesFinal(SFT<CharPred, CharFunc, Character> trans, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) throws TimeoutException {
		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		Collection<Integer> states = trans.getStates();
		
		for (Integer state : states) {
			finStatesAndTails.put(state, new HashSet<List<Character>>());
		}
		
		return SFT.MkSFT(trans.getTransitions(), trans.getInitialState(), finStatesAndTails, ba);
	}
	
	/* Remove final states */
	public static SFT<CharPred, CharFunc, Character> removeFinalStates(SFT<CharPred, CharFunc, Character> trans, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) throws TimeoutException {
		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		
		return SFT.MkSFT(trans.getTransitions(), trans.getInitialState(), finStatesAndTails, ba);
	}
	
	/* Variant of getDomain that does not normalize */
	public static SFA<CharPred, Character> getDomain(SFT<CharPred, CharFunc, Character> trans, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) throws TimeoutException {
		Collection<SFAMove<CharPred, Character>> transitions = new ArrayList<SFAMove<CharPred, Character>>();

		for (SFTInputMove<CharPred, CharFunc, Character> t : trans.getInputMovesFrom(trans.getStates()))
			transitions.add(new SFAInputMove<CharPred, Character>(t.from, t.to, t.guard));

		for (SFTEpsilon<CharPred, CharFunc, Character> t : trans.getEpsilonMovesFrom(trans.getStates()))
			transitions.add(new SFAEpsilon<CharPred, Character>(t.from, t.to));

		Collection<Integer> finalStates = trans.getFinalStates();

		return SFA.MkSFA(transitions, trans.getInitialState(), finalStates, ba, false, false);
	}
	
}
