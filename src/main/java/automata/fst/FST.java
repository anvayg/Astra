package automata.fst;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import automata.Automaton;
import automata.FAutomaton;
import automata.Move;
import automata.fsa.FSAMove;

public class FST<P, S> extends FAutomaton<P> {
	
	protected Collection<Integer> states;
	protected Integer initialState;
	protected Collection<Integer> finalStates;
	protected Integer maxStateId;
	private Integer transitionCount;

	// Moves
	protected Map<Integer, Collection<FSTMove<P, S>>> transitionsFrom;
	protected Map<Integer, Collection<FSTMove<P, S>>> transitionsTo;
	
	public FST() {
		super();
		this.finalStates = new HashSet<Integer>();
		this.states = new HashSet<Integer>();
		transitionsFrom = new HashMap<Integer, Collection<FSTMove<P, S>>>();
		transitionsTo = new HashMap<Integer, Collection<FSTMove<P, S>>>();
		transitionCount = 0;
		maxStateId = 0;
	}
	
	public static <P, S> FST<P, S> MkFST(Collection<FSTMove<P, S>> transitions, Integer initialState, 
			Collection<Integer> finalStates) {
		FST<P, S> aut = new FST<P, S>();
		
		// Initialize state set
		aut.states = new HashSet<Integer>();
		aut.states.add(initialState);
		for (Integer state : finalStates) {
			aut.states.add(state);
		}
		
		aut.initialState = initialState;
		aut.finalStates = finalStates;
		
		for (FSTMove<P, S> t : transitions) {
			aut.addTransition(t);
		}
		
		return aut;
	}
	
	private void addTransition(FSTMove<P, S> transition) {
		if (transition.from > maxStateId)
			maxStateId = transition.from;
		if (transition.to > maxStateId)
			maxStateId = transition.to;

		states.add(transition.from);
		states.add(transition.to);
		
		getTransitionsFrom(transition.from).add((FSTMove<P, S>) transition);
		getTransitionsTo(transition.to).add((FSTMove<P, S>) transition);
		transitionCount++;
	}
	
	public String toDotString() {
		StringBuilder sb = new StringBuilder();
		Collection<Integer> finStates = getFinalStates();
		
		sb.append("digraph {\n");
		for (Integer state : states) {
			if (finStates.contains(state)) {
				sb.append(state + " " + "[label=\"" + state + "\", peripheries = 2];\n");
			} else {
				sb.append(state + " " + "[label=\"" + state + "\"];\n");
			}
		}
		
		for (Integer state : states) {
			Collection<FSTMove<P, S>> transitions = getTransitionsFrom(state);
			for (FSTMove<P, S> t : transitions) {
				sb.append(t.toDotString());
			}
		}
		sb.append("}");
		
		return sb.toString();
	}
	
	private Collection<FSTMove<P, S>> getTransitionsFrom(Integer state) {
		Collection<FSTMove<P, S>> trset = transitionsFrom.get(state);
		if (trset == null) {
			trset = new HashSet<FSTMove<P, S>>();
			transitionsFrom.put(state, trset);
			return trset;
		}
		return trset;
	}

	private Collection<FSTMove<P, S>> getTransitionsTo(Integer state) {
		Collection<FSTMove<P, S>> trset = transitionsTo.get(state);
		if (trset == null) {
			trset = new HashSet<FSTMove<P, S>>();
			transitionsTo.put(state, trset);
			return trset;
		}
		return trset;
	}

	public Integer stateCount() {
		return states.size();
	}

	public Integer transitionCount() {
		return transitionCount;
	}

	@Override
	public Collection<Integer> getFinalStates() {
		return finalStates;
	}

	@Override
	public Integer getInitialState() {
		return initialState;
	}

	@Override
	public Collection<Integer> getStates() {
		return states;
	}

}
