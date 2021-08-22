package automata.fsa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import automata.FAutomaton;
import automata.fst.FSTMove;


/**
 * @author anvaygrover
 *
 * @param <P>
 * @param <S>
 */
public class FSA<P> extends FAutomaton<P> {
	
	protected Integer initialState;
	protected Collection<Integer> states;
	protected Collection<Integer> finalStates;

	protected Map<Integer, Collection<FSAMove<P>>> inputMovesFrom;
	protected Map<Integer, Collection<FSAMove<P>>> inputMovesTo;
	
	protected Integer maxStateId;
	protected Integer transitionCount;

	public FSA() {
		super();
		this.finalStates = new HashSet<Integer>();
		this.states = new HashSet<Integer>();
		inputMovesFrom = new HashMap<Integer, Collection<FSAMove<P>>>();
		inputMovesTo = new HashMap<Integer, Collection<FSAMove<P>>>();
		transitionCount = 0;
		maxStateId = 0;
	}
	
	public static <P> FSA<P> MkFSA(Collection<FSAMove<P>> transitions, Integer initialState, 
			Collection<Integer> finalStates) {
		FSA<P> aut = new FSA<P>();
		
		aut.states = new HashSet<Integer>();
		aut.states.add(initialState);
		aut.states.addAll(finalStates);

		aut.initialState = initialState;
		aut.finalStates = finalStates;
		
		for (FSAMove<P> t : transitions)
			aut.addTransition(t);
		
		return aut;
	}
	
	private void addTransition(FSAMove<P> transition) {
		if (transition.from > maxStateId)
			maxStateId = transition.from;
		if (transition.to > maxStateId)
			maxStateId = transition.to;

		states.add(transition.from);
		states.add(transition.to);
		
		getInputMovesFrom(transition.from).add((FSAMove<P>) transition);
		getInputMovesTo(transition.to).add((FSAMove<P>) transition);
		transitionCount++;
	}
	
	public List<Integer> inverseDeltaStates(Integer state, P input) {
		List<Integer> states = new ArrayList<Integer>();
		
		for (FSAMove<P> transition : getInputMovesTo(state)) {
			if (transition.input == input) {
				states.add(transition.from);
			}
		}
		
		return states;
	}
	
	public Integer getSuccessorState(Integer state, P input) {
		for (FSAMove<P> transition : getInputMovesFrom(state)) {
			if (transition.input == input) {
				return transition.to; 		// assumes disjoint transitions
			}
		}
		
		return -1; 	// no state found
	}
	
	public List<Integer> getRunOn(List<P> inputs) {
		List<P> inputsCopy = new ArrayList<P>(inputs);
		List<Integer> run = new ArrayList<Integer>();
		Collections.reverse(inputsCopy);
		
		Integer state = getInitialState();
		for (P input : inputsCopy) {
			Integer nextState = this.getSuccessorState(state, input);
			run.add(nextState);
			state = nextState;
		}
		
		Collections.reverse(run);
		return run;
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
			Collection<FSAMove<P>> transitions = getInputMovesFrom(state);
			for (FSAMove<P> t : transitions) {
				sb.append(t.toDotString());
			}
		}
		sb.append("}");
		
		return sb.toString();
	}
	
	public Integer stateCount() {
		return states.size();
	}

	public Integer transitionCount() {
		return transitionCount;
	}
	
	public Collection<FSAMove<P>> getTransitionsFrom(Integer state) {
		return getInputMovesFrom(state);
	}
	
	public Collection<FSAMove<P>> getTransitionsTo(Integer state) {
		return getInputMovesTo(state);
	}

	private Collection<FSAMove<P>> getInputMovesFrom(Integer state) {
		Collection<FSAMove<P>> trset = inputMovesFrom.get(state);
		if (trset == null) {
			trset = new HashSet<FSAMove<P>>();
			inputMovesFrom.put(state, trset);
			return trset;
		}
		return trset;
	}
	
	private Collection<FSAMove<P>> getInputMovesTo(Integer state) {
		Collection<FSAMove<P>> trset = inputMovesTo.get(state);
		if (trset == null) {
			trset = new HashSet<FSAMove<P>>();
			inputMovesTo.put(state, trset);
			return trset;
		}
		return trset;
	}
	
	public Collection<FSAMove<P>> getTransitionsFrom(Collection<Integer> states) {
		Collection<FSAMove<P>> trset = new HashSet<FSAMove<P>>();
		
		for (Integer state : states) {
			trset.addAll(this.getTransitionsFrom(state));
		}
		
		return trset;
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
