package automata;

import java.util.Collection;

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
			Character witness = transition.getWitness(ba);
			if (witness == move) {
				return transition.to;
			}
		}
		
		// should be unreachable
		return 0;
	}
}
