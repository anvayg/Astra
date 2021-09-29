package automata;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.commons.lang3.tuple.ImmutablePair;
import org.sat4j.specs.TimeoutException;

import com.google.common.collect.ImmutableList;

import RegexParser.CharNode;
import RegexParser.CharacterClassNode;
import RegexParser.ConcatenationNode;
import RegexParser.FormulaNode;
import RegexParser.IntervalNode;
import RegexParser.NormalCharNode;
import RegexParser.MetaCharNode;
import RegexParser.RegexListNode;
import RegexParser.RegexNode;
import RegexParser.StarNode;
import RegexParser.UnionNode;
import automata.fsa.FSA;
import automata.fsa.FSAMove;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import utilities.SFAprovider;

public class RegexFSA {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	private FSA<RegexNode> regexAut;
	
	public FSA<RegexNode> getRegexAut() {
		return regexAut;
	}

	/* 
	 * Convert SFA to a FSA labeled by RegexNodes 
	 * */
	public RegexFSA(SFA<CharPred, Character> aut) {
		ArrayList<FSAMove<RegexNode>> newTransitions = new ArrayList<FSAMove<RegexNode>>();
		
		for (SFAInputMove<CharPred, Character> transition : aut.getInputMovesFrom(aut.getStates())) {
			CharPred guard = transition.guard;
			
			// Get intervals
			ImmutableList<ImmutablePair<Character, Character>> intervals = guard.intervals;
			
			// Make list of IntervalNodes
			List<IntervalNode> intervalNodeList = new ArrayList<IntervalNode>();
			
			for (ImmutablePair<Character, Character> interval : intervals) {
				IntervalNode intervalNode = null;
				
				// hacky (TODO: implement in a more general fashion)
				if (interval.getLeft() == '\t' && interval.getRight() == '\r') {
					MetaCharNode left = new MetaCharNode('t');
					MetaCharNode right = new MetaCharNode('r');
					intervalNode = new IntervalNode(left, right);
					
				} else if (interval.getLeft() == interval.getRight()) {
					NormalCharNode left = new NormalCharNode(interval.getLeft());
					intervalNode = new IntervalNode(left);
					
				} else {
					NormalCharNode left = new NormalCharNode(interval.getLeft());
					NormalCharNode right = new NormalCharNode(interval.getRight());
					intervalNode = new IntervalNode(left, right);
				}
				
				intervalNodeList.add(intervalNode);
			}
			
			// Make character class for this CharPred
			CharacterClassNode charClass = new CharacterClassNode(intervalNodeList);

			// Make RegexNode
			LinkedList<RegexNode> concatList = new LinkedList<RegexNode>();
			concatList.add(charClass);
			RegexNode regex = new ConcatenationNode(concatList);
			
			// Add transition
			FSAMove<RegexNode> newTransition = new FSAMove<RegexNode>(transition.from, transition.to, regex);
			newTransitions.add(newTransition);
		}
		
		// Make FSA using transitions
		this.regexAut = FSA.MkFSA(newTransitions, aut.getInitialState(), aut.getFinalStates());
	}
	
	/* 
	 * Specially implemented toDotString because the RegexNode.toString methods modifies a StringBuilder
	 */
	public String toDotString() {
		StringBuilder sb = new StringBuilder();
		Collection<Integer> finStates = regexAut.getFinalStates();
		
		sb.append("digraph {\n");
		for (Integer state : regexAut.getStates()) {
			if (finStates.contains(state)) {
				sb.append(state + " " + "[label=\"" + state + "\", peripheries = 2];\n");
			} else {
				sb.append(state + " " + "[label=\"" + state + "\"];\n");
			}
		}
		
		for (Integer state : regexAut.getStates()) {
			Collection<FSAMove<RegexNode>> transitions = regexAut.getTransitionsFrom(state);
			for (FSAMove<RegexNode> t : transitions) {
				StringBuilder regexString = new StringBuilder();
				
				prettyPrint(t.input, regexString, null, 0);
				sb.append(String.format("%s -> %s [label=\"%s\"]\n", t.from, t.to, regexString.toString()));
			}
		}
		sb.append("}");
		
		return sb.toString();
	}
	
	/* 
	 * Remove states from FSA to obtain a regular expression
	 */
	public void stateElimination() {
		// Epsilon transitions are empty ConcatenationNodes
		RegexNode epsilon = new ConcatenationNode(new LinkedList<RegexNode>());
		
		// Ensure initial state has no incoming transitions
		Integer initState = regexAut.getInitialState();
		Collection<FSAMove<RegexNode>> transitionsToInit = regexAut.getTransitionsTo(initState);
		if (transitionsToInit != null && transitionsToInit.size() > 0) {
			Integer newInitState = regexAut.getMaxStateId() + 1;
			
			// Make new epsilon transition
			ArrayList<FSAMove<RegexNode>> newTransitions = new ArrayList<FSAMove<RegexNode>>();
			newTransitions.addAll(regexAut.getTransitionsFrom(regexAut.getStates()));
			newTransitions.add(new FSAMove<RegexNode>(newInitState, initState, epsilon));
			
			regexAut = FSA.MkFSA(newTransitions, newInitState, regexAut.getFinalStates());
		}
		
		// Ensure there is only 1 final state and it has no outgoing transitions
		Collection<Integer> finalStates = regexAut.getFinalStates();
		boolean mkNewFinState = false;
		if (finalStates.size() > 1) {
			mkNewFinState = true;
		} else if (finalStates.size() == 1) {
			// Outgoing transitions
			for (Integer finState : finalStates) {
				Collection<FSAMove<RegexNode>> transitionsFromFin = regexAut.getTransitionsFrom(finState);
				
				if (transitionsFromFin != null && transitionsFromFin.size() > 0) 
					mkNewFinState = true;
			}
		} else {
			// No final states -> empty regex
			ArrayList<FSAMove<RegexNode>> newTransitions = new ArrayList<FSAMove<RegexNode>>();
			Integer newInitState = regexAut.getMaxStateId() + 1;
			Integer newFinState = regexAut.getMaxStateId() + 2;
			newTransitions.add(new FSAMove<RegexNode>(newInitState, newFinState, epsilon));
			
			ArrayList<Integer> finStateList = new ArrayList<Integer>();
			finStateList.add(newFinState);
			regexAut = FSA.MkFSA(newTransitions, newInitState, finStateList); 	// Only 2 states
		}
		
		if (mkNewFinState) {
			Integer newFinState = regexAut.getMaxStateId() + 1;
			ArrayList<FSAMove<RegexNode>> newTransitions = new ArrayList<FSAMove<RegexNode>>();
			newTransitions.addAll(regexAut.getTransitionsFrom(regexAut.getStates()));
			
			for (Integer finState : finalStates) {
				// Make new epsilon transition from old final state to the new one
				newTransitions.add(new FSAMove<RegexNode>(finState, newFinState, epsilon));
			}
			
			ArrayList<Integer> finStateList = new ArrayList<Integer>();
			finStateList.add(newFinState);
			regexAut = FSA.MkFSA(newTransitions, regexAut.getInitialState(), finStateList);
		}
		
		// Eliminate states other than initial and final
		for (Integer state : regexAut.getStates()) {
			if (regexAut.getInitialState() == state) continue;
			
			if (regexAut.getFinalStates().contains(state)) continue;
			
			// Find self-loop if there is one
			Collection<FSAMove<RegexNode>> transitionsOut = regexAut.getTransitionsFrom(state);
			StarNode selfLoop = null;
			for (FSAMove<RegexNode> t : transitionsOut) {
				if (t.to == state)
					selfLoop = new StarNode(t.input);
			}
			
			// Consider all combinations of 'from' and 'to' states
			Collection<FSAMove<RegexNode>> newTransitions = new HashSet<FSAMove<RegexNode>>();
			
			Collection<FSAMove<RegexNode>> transitionsIn = regexAut.getTransitionsTo(state);
			for (FSAMove<RegexNode> transitionIn : transitionsIn) {
				for (FSAMove<RegexNode> transitionOut : transitionsOut) {
					Integer newFrom = transitionIn.from;
					Integer newTo = transitionOut.to;
					
					if (newFrom == state || newTo == state)
						continue;
					
					RegexNode regexIn = transitionIn.input;
					RegexNode regexOut = transitionOut.input;
					RegexNode newRegex = null;
					
					if (selfLoop != null) {
						LinkedList<RegexNode> concatList = new LinkedList<RegexNode>();
						concatList.add(regexIn);
						concatList.add(selfLoop);
						concatList.add(regexOut);
						newRegex = new ConcatenationNode(concatList);
					} else {
						LinkedList<RegexNode> concatList = new LinkedList<RegexNode>();
						concatList.add(regexIn);
						concatList.add(regexOut);
						newRegex = new ConcatenationNode(concatList);
					}
					
					newTransitions.add(new FSAMove<RegexNode>(newFrom, newTo, newRegex));
				}
			}
			
			// New set of transitions for regexAut
			Collection<FSAMove<RegexNode>> newTransitionSet = new HashSet<FSAMove<RegexNode>>();
			newTransitionSet.addAll(regexAut.getTransitionsFrom(regexAut.getStates()));
			newTransitionSet.removeAll(transitionsIn);
			newTransitionSet.removeAll(transitionsOut);
			newTransitionSet.addAll(newTransitions);
			
			// New automaton
			regexAut = FSA.MkFSA(newTransitionSet, regexAut.getInitialState(), regexAut.getFinalStates());
			
			// Union of transitions from and to the same states
			normalizeRegexFSA();
		}
	}
	
	public void normalizeRegexFSA() {
		Collection<FSAMove<RegexNode>> newTransitions = new HashSet<FSAMove<RegexNode>>();
		
		for (Integer state : regexAut.getStates()) {
			if (regexAut.getFinalStates().contains(state)) continue; 	// We will not insert transitions out of the final state
			
			Set<Integer> alreadySeen = new HashSet<Integer>();
			
			Collection<FSAMove<RegexNode>> transitionsOut = regexAut.getTransitionsFrom(state);
			for (FSAMove<RegexNode> t1 : transitionsOut) {
				Integer stateTo = t1.to;
				
				// If we have already seen this state, then all transitions to it would have already been combined
				if (alreadySeen.contains(stateTo)) continue;
				
				alreadySeen.add(stateTo);
				
				Collection<FSAMove<RegexNode>> commonTransitions = new HashSet<FSAMove<RegexNode>>();
				
				// Inner for-loop finds any other transitions to the same state
				for (FSAMove<RegexNode> t2 : transitionsOut) {
					if (t2.to == stateTo)
						commonTransitions.add(t2);
				}
				
				// Combine transitions if any more were found
				if (commonTransitions.size() > 1) {
					FSAMove<RegexNode>[] transitions = 
							(FSAMove<RegexNode>[]) commonTransitions.toArray(new FSAMove<?> [commonTransitions.size()]);
					
					// Take union
					RegexNode unionRegex = transitions[0].input;
					for (int i = 1; i < transitions.length; i++) {
						if (transitions[i].input != null)
							unionRegex = new UnionNode(unionRegex, transitions[i].input);
					}
					newTransitions.add(new FSAMove<RegexNode>(state, stateTo, unionRegex));
					
					
				} else {	// Keep original transitions if no other transitions go to the same state from this one
					newTransitions.add(t1);
				}
				
			}
		}
		
		// New automaton
		regexAut = FSA.MkFSA(newTransitions, regexAut.getInitialState(), regexAut.getFinalStates());
	}
	
	/* 
	 * Format RegexNode after state elimination to return regex
	 */
	public String formatRegex() {
		Collection<FSAMove<RegexNode>> transition = regexAut.getTransitionsFrom(regexAut.getInitialState());
		
		int counter = 0;
		RegexNode regex =  null;
		for (FSAMove<RegexNode> t : transition) {
			if (counter == 1) throw new IllegalArgumentException("State elimination failed: more than 1 transition");
			
			if (t.input == null) return "";
			
			regex = t.input;
		}
		
		StringBuilder sb = new StringBuilder();
		regex.toString(sb);
		
		String regexString = sb.toString();
		regexString = regexString.replaceAll("Char:", "");
		regexString = regexString.replaceAll("Meta:", "\\\\");
		regexString = regexString.replaceAll(" ]", "]");
//		regexString = regexString.replaceAll("\\(\\(\\(", "\\(");
//		regexString = regexString.replaceAll("\\)\\)\\)", "\\)");
//		regexString = regexString.replaceAll("\\)\\(", "\\) . \\(");
//		regexString = regexString.replaceAll("\\*\\)", "\\* \\)");
		regexString = regexString.replaceAll("\\(", "");
		regexString = regexString.replaceAll("\\)", "");
		regexString = regexString.replaceAll("\\]\\[", "\\] . \\[");
		regexString = regexString.replaceAll("\\*\\[", "\\* . \\[");
		return regexString;
	}
	
	/* 
	 * Should be called post state-elimination
	 */
	public RegexNode getRegexNode() {
		Collection<FSAMove<RegexNode>> transition = regexAut.getTransitionsFrom(regexAut.getInitialState());
		
		for (FSAMove<RegexNode> t : transition) {
			return t.input;
		}
		
		return null;
	}
	
	// Recurse over the structure of the RegexNode
	public void prettyPrint(RegexNode r, StringBuilder sb, String printMode, int depth) {
		// Going with the instanceOf approach since every other solution seems clunky as well
		// Not using depth currently
		
		if (sb == null)
			sb = new StringBuilder();
		
		if (r instanceof UnionNode) {
			UnionNode regex = (UnionNode) r;
			RegexNode myRegex1 = regex.getMyRegex1();
			RegexNode myRegex2 = regex.getMyRegex2();
			
			sb.append("(");
			prettyPrint(myRegex1, sb, printMode, depth++);
			sb.append(" | ");
			prettyPrint(myRegex2, sb, printMode, depth++);
			sb.append(")");
			
		} else if (r instanceof ConcatenationNode) {
			ConcatenationNode regex = (ConcatenationNode) r;
			List<RegexNode> concatList = regex.getList();
			
			if (concatList.size() == 0)
				sb.append("\"\"");
			
			if (concatList.size() > 1)
				sb.append("(");
			
			Iterator<RegexNode> it = concatList.iterator();
			while (it.hasNext()) {
				RegexNode r1 = it.next();
				prettyPrint(r1, sb, printMode, depth++);
				
				if (printMode != null && printMode.equals("lenses") && it.hasNext()) {
					sb.append(" . ");
				}
			}
			
			if (concatList.size() > 1)
				sb.append(")");
			
		} else if (r instanceof StarNode) {
			StarNode regex = (StarNode) r;
			RegexNode myRegex1 = regex.getMyRegex1();
			
			prettyPrint(myRegex1, sb, printMode, depth++);
			sb.append("*");
			
		} else if (r instanceof CharacterClassNode) {
			CharacterClassNode regex = (CharacterClassNode) r;
			List<IntervalNode> intervalsList = regex.getIntervals();
			
			sb.append("[");
			for (IntervalNode i : intervalsList) {
				prettyPrint(i, sb, printMode, depth++);
			}
			sb.append("]");
		
		} else if (r instanceof IntervalNode) {
			IntervalNode regex = (IntervalNode) r;
			CharNode myChar1 = regex.getChar1();
			CharNode myChar2 = null;
			String mode = regex.getMode();
			
			if (mode.equals("single")) {
				prettyPrint(myChar1, sb, mode, depth++);
			} else {
				myChar2 = regex.getChar2();
				prettyPrint(myChar1, sb, mode, depth++);
				sb.append("-");
				prettyPrint(myChar2, sb, mode, depth++);
			}	
			
		} else if (r instanceof NormalCharNode) {
			NormalCharNode regex = (NormalCharNode) r;
			char myChar = regex.getChar();
			
			sb.append(myChar);
			
		} else if (r instanceof MetaCharNode) {
			MetaCharNode regex = (MetaCharNode) r;
			char myChar = regex.getChar();
			
			sb.append("\\");
			sb.append(myChar);
			
		} else {
			throw new IllegalArgumentException("This RegexNode is currently not supported.");
			
		}
		
	}
	
	/* Returns the equivalent regular expression of a regexFSA */
	public String toRegex() {
		this.stateElimination();
		
		StringBuilder sb = new StringBuilder();
		prettyPrint(getRegexNode(), sb, "lenses", 0);
		return sb.toString();
	}
	
	private static List<Character> lOfS(String s) {
		List<Character> l = new ArrayList<Character>();
		char[] ca = s.toCharArray();
		for (int i = 0; i < s.length(); i++)
			l.add(ca[i]);
		return l;
	}
	
	public static void main(String[] args) throws TimeoutException {
		String CONFERENCE_NAME_REGEX = "[A-Z][a-z]*( [A-Z][a-z]*)*";
		SFA<CharPred, Character> CONFERENCE_NAME = (new SFAprovider(CONFERENCE_NAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(CONFERENCE_NAME.accepts(lOfS("Principles Of Programming Languages"), ba));
		System.out.println(CONFERENCE_NAME.toDotString(ba));
		
		RegexFSA regexFSA = new RegexFSA(CONFERENCE_NAME);
		CONFERENCE_NAME_REGEX = regexFSA.toRegex();
		System.out.println(CONFERENCE_NAME_REGEX);
	}
	
}