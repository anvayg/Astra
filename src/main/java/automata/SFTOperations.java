package automata;

import java.util.Collection;

import org.sat4j.specs.TimeoutException;

import theory.BooleanAlgebra;
import theory.BooleanAlgebraSubst;
import theory.characters.CharConstant;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import transducers.sft.*;

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
}
