package automata.fst;

import java.util.List;

import automata.FMove;

public class FSTMove<P, S> extends FMove {
	
	public P input;
	public List<S> outputs;

	public FSTMove(Integer from, Integer to, P input, List<S> outputs) {
		super(from, to);
		this.input = input;
		this.outputs = outputs;
	}

	public String toDotString() {
		StringBuilder label = new StringBuilder(input + " / ");
		
		for (S output : outputs) {
			label.append(output.toString());
		}
		
		return String.format("%s -> %s [label=\"%s\"]\n", from, to, label.toString());
	}
}
