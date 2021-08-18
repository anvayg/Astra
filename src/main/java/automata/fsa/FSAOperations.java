package automata.fsa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import org.sat4j.specs.TimeoutException;

import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;
import theory.BooleanAlgebraSubst;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import utilities.Pair;

public class FSAOperations {
	public static SFA<CharPred, Character> mintermExpansion(FSA<Character> aut,
			Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterm, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) throws TimeoutException {
		
		Collection<SFAMove<CharPred, Character>> newTransitions = new ArrayList<SFAMove<CharPred, Character>>();
		for (Integer state : aut.getStates()) {
			for (FSAMove<Character> transition : aut.getTransitionsFrom(state)) {
				Character c = transition.input;
				CharPred pred = idToMinterm.get(new CharPred(c)).first;
				
				SFAInputMove<CharPred, Character> newTransition = new SFAInputMove<CharPred, Character>(transition.from, transition.to, pred);
				newTransitions.add(newTransition);
			}
		}
		
		return SFA.MkSFA(newTransitions, aut.getInitialState(), aut.getFinalStates(), ba, false, false);
		
	}
}
