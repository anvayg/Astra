package automata;

import java.util.Collection;
import java.util.LinkedList;

import theory.characters.CharFunc;
import theory.characters.CharPred;
import transducers.sft.SFT;
import transducers.sft.SFTInputMove;

public class SFTTemplate {
	
	/* Instance variables */
	private SFT<CharPred, CharFunc, Character> aut;
	private Collection<SFTInputMove<CharPred, CharFunc, Character>> goodTransitions;
	private Collection<SFTInputMove<CharPred, CharFunc, Character>> badTransitions;
	
	public SFTTemplate(SFT<CharPred, CharFunc, Character> aut, 
			Collection<SFTInputMove<CharPred, CharFunc, Character>> badTransitions) {
		this.aut = aut;
		this.badTransitions = badTransitions;
		
		Collection<SFTInputMove<CharPred, CharFunc, Character>> currentTransitions = new LinkedList<SFTInputMove<CharPred, CharFunc, Character>>();

		for (Integer state : aut.getStates()) {
			currentTransitions.addAll(aut.getInputMovesFrom(state));
		}
		
		currentTransitions.removeAll(badTransitions);
		this.goodTransitions = currentTransitions;
	}
	
	public SFT<CharPred, CharFunc, Character> getAut() {
		return aut;
	}
	
	public Collection<SFTInputMove<CharPred, CharFunc, Character>> getGoodTransitions() {
		return goodTransitions;
	}
	
	public Collection<SFTInputMove<CharPred, CharFunc, Character>> getBadTransitions() {
		return badTransitions;
	}
	
}
