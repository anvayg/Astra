package automata.fst;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import automata.FAutomaton;
import automata.fsa.FSA;
import utilities.Pair;

public class FSTLookahead<P, S> extends FAutomaton<P> {
	
	protected FST<Pair<P, Integer>, S> fst;
	protected FSA<P> aut;
	
	public FSTLookahead(FST<Pair<P, Integer>, S> fst, FSA<P> aut) {
		super();
		this.fst = fst;
		this.aut = aut;
	}
	
	public FST<Pair<P, Integer>, S> getTransducer() {
		return this.fst;
	}
	
	public FSA<P> getAutomaton() {
		return this.aut;
	}
	
	public Integer getSuccessorState(Integer state, P input, Integer lookaheadState) {
		for (FSTMove<Pair<P, Integer>, S> transition : fst.getTransitionsFrom(state)) {
			if (transition.input.first == input) {
				if (transition.input.second == lookaheadState || lookaheadState == -1) {
					return transition.to;
				}
			}
		}
		
		return -1;
	}
	
	public List<S> outputOn(List<P> inputs) {
		List<S> outputs = new ArrayList<S>();
		
		List<Integer> runOnAut = this.aut.getRunOn(inputs);
		Integer state = getInitialState();
		for (int i = 0; i < inputs.size(); i++) {
			P input = inputs.get(i);
			Integer lookaheadState = -1;
			if (i < inputs.size() - 1) {
				lookaheadState = runOnAut.get(i + 1);
			}
			
			// take correct transition
			for (FSTMove<Pair<P, Integer>, S> transition : fst.getTransitionsFrom(state)) {
				if (transition.input.first == input) {
					if (transition.input.second == lookaheadState || lookaheadState == -1) {
						outputs.addAll(transition.outputs);
						state = transition.to;
						break;
					}
				}
			}
			
		}
		
		return outputs;
	}

	@Override
	public Collection<Integer> getStates() {
		return fst.getStates();
	}

	@Override
	public Integer getInitialState() {
		return fst.getInitialState();
	}

	@Override
	public Collection<Integer> getFinalStates() {
		return fst.getFinalStates();
	}
	
}
