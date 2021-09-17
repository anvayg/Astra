package automata;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.tuple.ImmutablePair;
import org.sat4j.specs.TimeoutException;

import automata.fst.FST;
import automata.fst.FSTMove;
import automata.sfa.SFA;
import automata.sfa.SFAEpsilon;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;
import theory.BooleanAlgebraSubst;
import theory.characters.CharConstant;
import theory.characters.CharFunc;
import theory.characters.CharOffset;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import transducers.sft.SFTEpsilon;
import transducers.sft.SFTInputMove;
import transducers.sft.SFTMove;
import utilities.Pair;

public class SFTOperations {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	/* 
	 * Returns output string given a transducer and an input string. Assumes the alphabet of
	 * trans includes the character in inputStr. This function is meant for a finite 
	 * transducer, i.e., where the output functions are constants.
	 */
	public static String getOutputString(SFT<CharPred, CharFunc, Character> trans, String inputStr) throws TimeoutException {
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
	
	/* 
	 * Returns the list of transitions taken by an input string on a transducer, in order
	 */
	public static List<SFTInputMove<CharPred, CharFunc, Character>> getTransitionsTaken(SFT<CharPred, CharFunc, Character> trans, String inputStr) throws TimeoutException {
		List<SFTInputMove<CharPred, CharFunc, Character>> transitionsTaken = new ArrayList<SFTInputMove<CharPred, CharFunc, Character>>();
		Integer state = trans.getInitialState();
		
		for (int i = 0; i < inputStr.length(); i++) {
			Character next = inputStr.charAt(i);
			Collection<SFTInputMove<CharPred, CharFunc, Character>> transitions = trans.getInputMovesFrom(state);
			
			for (SFTInputMove<CharPred, CharFunc, Character> transition : transitions) {
				if (transition.guard.isSatisfiedBy(next)) { 	// only 1 transition should be sat
					transitionsTaken.add(transition);
					
					state = transition.to;
				}
			}
		}
		
		
		return transitionsTaken;
	}
	
	/* 
	 * Based on SFT.OutputOn but returns all outputs of a non-det transducer
	 * */
	public static List<String> getAllOutputs(SFT<CharPred, CharFunc, Character> trans, String inputStr, 
			BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) throws TimeoutException {
		
		List<List<Character>> outputs = new ArrayList<List<Character>>();
		
		backtrack(outputs, new ArrayList<Character>(), trans, trans.getInitialState(), lOfS(inputStr), 0, ba);
		
		List<String> outputStrings = new ArrayList<String>();
		for (List<Character> l : outputs) {
			outputStrings.add(sOfL(l));
		}
		
		return outputStrings;
	}
	
	private static <P, F, S> void backtrack(List<List<S>> outputs, List<S> tempList, SFT<P, F, S> sft,
			Integer currentState, List<S> input, int position, BooleanAlgebraSubst<P, F, S> ba) throws TimeoutException {

		if (position > input.size())
			return;
		else if (position == input.size()) {
			if (sft.isFinalState(currentState)) {
				if (sft.getFinalStatesAndTails().get(currentState).size() == 0) {
					outputs.add(new ArrayList<S>(tempList));
				} else {
					for (List<S> tail: sft.getFinalStatesAndTails().get(currentState)) {
						List<S> finalResult = new ArrayList<S>(tempList);
						finalResult.addAll(tail);
						outputs.add(new ArrayList<S>(finalResult));
					}
				}
			}
			return;
		} else {
			Collection<SFTInputMove<P, F, S>> transitions = sft.getInputMovesFrom(currentState);
			boolean canMove = false;
			for (SFTInputMove<P, F, S> transition: transitions) {
				if (ba.HasModel(transition.guard, input.get(position))) {
					for (F outputFunc: transition.outputFunctions)
						tempList.add(ba.MkSubstFuncConst(outputFunc, input.get(position)));
					backtrack(outputs, tempList, sft, transition.to, input, position + 1, ba);
					for (int i = 0; i < transition.outputFunctions.size(); i++)
						tempList.remove(tempList.size() - 1);
					canMove = true;
				}
			}
			if (!canMove)
				return;
		}
	}
	
	public static List<CharPred> getPreds(SFT<CharPred, CharFunc, Character> aut) {
		ArrayList<CharPred> predicates = new ArrayList<CharPred>(); 

		for (Integer state : aut.getStates()) {
			for (SFTInputMove<CharPred, CharFunc, Character> transition : aut.getInputMovesFrom(state)) {
				predicates.add(transition.guard);
			}
		}
		
		return predicates;
	}
	
	public static Collection<Pair<CharPred, ArrayList<Integer>>> getMinterms(SFT<CharPred, CharFunc, Character> aut) {
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
			Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterm) throws TimeoutException {
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
								CharPred inputMinterm = SFAOperations.findSatisfyingMinterm(c, idToMinterm).first;
								CharPred outputMinterm = SFAOperations.findSatisfyingMinterm(out, idToMinterm).first;
								
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
	public static SFT<CharPred, CharFunc, Character> mkAllStatesFinal(SFT<CharPred, CharFunc, Character> trans) throws TimeoutException {
		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		Collection<Integer> states = trans.getStates();
		
		for (Integer state : states) {
			finStatesAndTails.put(state, new HashSet<List<Character>>());
		}
		
		return SFT.MkSFT(trans.getTransitions(), trans.getInitialState(), finStatesAndTails, ba);
	}
	
	/* Remove final states */
	public static SFT<CharPred, CharFunc, Character> removeFinalStates(SFT<CharPred, CharFunc, Character> trans) throws TimeoutException {
		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		
		return SFT.MkSFT(trans.getTransitions(), trans.getInitialState(), finStatesAndTails, ba);
	}
	
	/* Variant of getDomain that does not normalize */
	public static SFA<CharPred, Character> getDomain(SFT<CharPred, CharFunc, Character> trans) throws TimeoutException {
		Collection<SFAMove<CharPred, Character>> transitions = new ArrayList<SFAMove<CharPred, Character>>();

		for (SFTInputMove<CharPred, CharFunc, Character> t : trans.getInputMovesFrom(trans.getStates()))
			transitions.add(new SFAInputMove<CharPred, Character>(t.from, t.to, t.guard));

		for (SFTEpsilon<CharPred, CharFunc, Character> t : trans.getEpsilonMovesFrom(trans.getStates()))
			transitions.add(new SFAEpsilon<CharPred, Character>(t.from, t.to));

		Collection<Integer> finalStates = trans.getFinalStates();

		return SFA.MkSFA(transitions, trans.getInitialState(), finalStates, ba, false, false);
	}
	
	/* Remove a set of transitions from an SFT */
	public static SFT<CharPred, CharFunc, Character> removeTransitions(SFT<CharPred, CharFunc, Character> aut, 
			Collection<SFTInputMove<CharPred, CharFunc, Character>> badTransitions) throws TimeoutException {
		Collection<SFTMove<CharPred, CharFunc, Character>> currentTransitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();

		for (Integer state : aut.getStates()) {
			currentTransitions.addAll(aut.getInputMovesFrom(state));
		}
		
		currentTransitions.removeAll(badTransitions);
		
		return SFT.MkSFT(currentTransitions, aut.getInitialState(), aut.getFinalStatesAndTails(), ba);
	}
	
	/* Returns the domain common to 2 SFTs */
	public static Pair<SFT<CharPred, CharFunc, Character>, SFA<CharPred, Character>> computeUnchangedDomain(SFT<CharPred, CharFunc, Character> trans, 
			SFT<CharPred, CharFunc, Character> modTrans) throws TimeoutException {
		LinkedList<SFTInputMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTInputMove<CharPred, CharFunc, Character>>();

		for (Integer state : trans.getStates()) {
			transitions.addAll(trans.getInputMovesFrom(state));
		}

		LinkedList<SFTInputMove<CharPred, CharFunc, Character>> modTransitions = new LinkedList<SFTInputMove<CharPred, CharFunc, Character>>();

		for (Integer state : modTrans.getStates()) {
			modTransitions.addAll(modTrans.getInputMovesFrom(state));
		}

		LinkedList<SFTMove<CharPred, CharFunc, Character>> unchangedTransitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();

		for (SFTInputMove<CharPred, CharFunc, Character> transition : transitions) {
			if (modTransitions.contains(transition)) {
				unchangedTransitions.add(transition);
			}
		}

		SFT<CharPred, CharFunc, Character> unchangedSFT = SFT.MkSFT(unchangedTransitions, trans.getInitialState(), trans.getFinalStatesAndTails(), ba);

		return new Pair<SFT<CharPred, CharFunc, Character>, SFA<CharPred, Character>>(unchangedSFT, unchangedSFT.getDomain(ba));
	}
	
	/* Returns the set of transitions that have been altered from trans to modTrans */
	public static Collection<SFTInputMove<CharPred, CharFunc, Character>> computeDiffTransitions(SFT<CharPred, CharFunc, Character> trans, 
			SFT<CharPred, CharFunc, Character> modTrans) throws TimeoutException {
		Collection<SFTInputMove<CharPred, CharFunc, Character>> diffTransitions = new ArrayList<SFTInputMove<CharPred, CharFunc, Character>>();
		
		LinkedList<SFTInputMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTInputMove<CharPred, CharFunc, Character>>();

		for (Integer state : trans.getStates()) {
			transitions.addAll(trans.getInputMovesFrom(state));
		}

		LinkedList<SFTInputMove<CharPred, CharFunc, Character>> modTransitions = new LinkedList<SFTInputMove<CharPred, CharFunc, Character>>();

		for (Integer state : modTrans.getStates()) {
			modTransitions.addAll(modTrans.getInputMovesFrom(state));
		}
		
		for (SFTInputMove<CharPred, CharFunc, Character> transition : modTransitions) {
			if (!transitions.contains(transition)) {
				diffTransitions.add(transition);
			}
		}
		
		return diffTransitions;
	}
	
	/* Finitize SFT to FST */
	public static FST<Character, Character> mkFinite(SFT<CharPred, CharFunc, Character> aut, 
			Collection<Pair<CharPred, ArrayList<Integer>>> minterms,
			Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterm,
			Map<Pair<CharPred, ArrayList<Integer>>, CharPred> mintermToId) throws TimeoutException {
		Collection<FSTMove<Character, Character>> transitions = new ArrayList<FSTMove<Character, Character>>();
		
		for (Integer state : aut.getStates()) {
			for (SFTInputMove<CharPred, CharFunc, Character> transition : aut.getInputMovesFrom(state)) {
				for (Pair<CharPred, ArrayList<Integer>> minterm : minterms) {
					CharPred conj = ba.MkAnd(transition.guard, minterm.first);
					if (ba.IsSatisfiable(conj)) {
						Character input = ba.generateWitness(mintermToId.get(minterm)); 	// should be one witness
						
						// Obtain outputs
						List<Character> outputs = new ArrayList<Character>();
						for (CharFunc f : transition.outputFunctions) {
							// use instantiate, then find satisfying minterm, and then reduce
							Character out = f.instantiateWith(input);
							Pair<CharPred, ArrayList<Integer>> satMinterm = SFAOperations.findSatisfyingMinterm(out, idToMinterm);
							
							outputs.add(ba.generateWitness(mintermToId.get(satMinterm)));
						}
						
						// add transition
						FSTMove<Character, Character> newTransition = 
								new FSTMove<Character, Character>(transition.from, transition.to, input, outputs);
						transitions.add(newTransition);
					}
				}
			}
		}
		
		return FST.MkFST(transitions, aut.getInitialState(), aut.getFinalStates());
	}
	
	/* Finite set of SFT transitions */
	public static Collection<FSTMove<Character, Character>> mkTransitionsFinite(Collection<SFTInputMove<CharPred, CharFunc, Character>> transitions, 
			Collection<Pair<CharPred, ArrayList<Integer>>> minterms,
			Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterm,
			Map<Pair<CharPred, ArrayList<Integer>>, CharPred> mintermToId) throws TimeoutException {
		Collection<FSTMove<Character, Character>> newTransitions = new ArrayList<FSTMove<Character, Character>>();
		
		for (SFTInputMove<CharPred, CharFunc, Character> transition : transitions) {
			for (Pair<CharPred, ArrayList<Integer>> minterm : minterms) {
				CharPred conj = ba.MkAnd(transition.guard, minterm.first);
				if (ba.IsSatisfiable(conj)) {
					Character input = ba.generateWitness(mintermToId.get(minterm)); 	// should be one witness
					
					// Obtain outputs
					List<Character> outputs = new ArrayList<Character>();
					for (CharFunc f : transition.outputFunctions) {
						Character out = f.instantiateWith(input);
						Pair<CharPred, ArrayList<Integer>> satMinterm = SFAOperations.findSatisfyingMinterm(out, idToMinterm);
						
						outputs.add(ba.generateWitness(mintermToId.get(satMinterm)));
					}
					
					// add transition
					FSTMove<Character, Character> newTransition = 
							new FSTMove<Character, Character>(transition.from, transition.to, input, outputs);
					newTransitions.add(newTransition);
				}
			}
		}
		
		return newTransitions;
	}
	
	/* Method for locating which transitions need to be repaired */
	public static Collection<SFTInputMove<CharPred, CharFunc, Character>> localizeFaults(SFT<CharPred, CharFunc, Character> aut, List<Pair<String, String>> examples) throws TimeoutException {
		Set<SFTInputMove<CharPred, CharFunc, Character>> badTransitions = new HashSet<SFTInputMove<CharPred, CharFunc, Character>>();
		
		for (Pair<String, String> example : examples) {
        	String exampleOutput = SFTOperations.getOutputString(aut, example.first);	// applies to deterministic transducers
        	List<SFTInputMove<CharPred, CharFunc, Character>> transitionsTaken = SFTOperations.getTransitionsTaken(aut, example.first);
        	
        	// Take the difference between the transitions of the buggy inputs and those of the correct inputs
        	if (!exampleOutput.equals(example.second)) {
        		badTransitions.addAll(transitionsTaken);
        	} else {
        		badTransitions.removeAll(transitionsTaken);
        	}
		}
		
		return badTransitions;
	}
	
	/* String from List of Chars */
	public static String sOfL(List<Character> l) {
		StringBuffer str = new StringBuffer();
		
		for (Character c : l) {
			str.append(c);
		}
		
		return str.toString();
	}
	
	private static List<Character> lOfS(String s) {
		List<Character> l = new ArrayList<Character>();
		char[] ca = s.toCharArray();
		for (int i = 0; i < s.length(); i++)
			l.add(ca[i]);
		return l;
	}
}
