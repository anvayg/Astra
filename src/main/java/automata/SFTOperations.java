package automata;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.sat4j.specs.TimeoutException;

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
						if (f != null && f instanceof CharConstant) {
							Character out = ((CharConstant)f).c;
							outputStr.append(out);
						}
					}
					state = transition.to;
				}
			}
		}
		
		return outputStr.toString();
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
								output.add(f);
							}
					}
				}
				newTransition.outputFunctions = output;
				
				newTransitions.add(newTransition);
			}
		}
		
		return SFT.MkSFT(newTransitions, trans.getInitialState(), trans.getFinalStatesAndTails(), ba);
	}
	
}
