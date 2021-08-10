package automata.fsa;

import automata.FMove;

public class FSAMove<P> extends FMove {

	public P input;
	
	public FSAMove(Integer from, Integer to, P input) {
		super(from, to);
		this.input = input;
	}

	public P getInputSymbol() {
		return input;
	}
	
	public String toDotString() {
		return String.format("%s -> %s [label=\"%s\"]\n", from, to, input);
	}
}
