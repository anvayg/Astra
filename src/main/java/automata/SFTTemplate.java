package automata;

import java.util.Collection;

import theory.characters.CharFunc;
import theory.characters.CharPred;
import transducers.sft.SFT;
import transducers.sft.SFTInputMove;

public class SFTTemplate {
	private SFT<CharPred, CharFunc, Character> aut;
	private Collection<SFTInputMove<CharPred, CharFunc, Character>> badTransitions;
	
	public SFTTemplate(SFT<CharPred, CharFunc, Character> aut,
			Collection<SFTInputMove<CharPred, CharFunc, Character>> badTransitions) {
		super();
		this.aut = aut;
		this.badTransitions = badTransitions;
	}

	public SFT<CharPred, CharFunc, Character> getAut() {
		return aut;
	}

	public Collection<SFTInputMove<CharPred, CharFunc, Character>> getBadTransitions() {
		return badTransitions;
	}
}
