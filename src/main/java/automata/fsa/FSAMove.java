package automata.fsa;

import automata.FMove;
import automata.fst.FSTMove;

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
	
	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof FSAMove<?>))
			return false;
		
		FSAMove<P> t = (FSAMove<P>) obj;
		
		if (t.from != this.from)
			return false;
		
		if (t.to != this.to)
			return false;
		
		if (t.input != this.input)
			return false;
		
		return true;
	}
}
