package automata;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.apache.commons.lang3.tuple.ImmutablePair;
import org.sat4j.specs.TimeoutException;

import com.google.common.collect.ImmutableList;

import RegexParser.CharacterClassNode;
import RegexParser.ConcatenationNode;
import RegexParser.FormulaNode;
import RegexParser.IntervalNode;
import RegexParser.NormalCharNode;
import RegexParser.RegexListNode;
import RegexParser.RegexNode;
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

	/* Convert SFA to a FSA labeled by RegexNodes */
	public RegexFSA(SFA<CharPred, Character> aut) {
		ArrayList<FSAMove<RegexNode>> newTransitions = new ArrayList<FSAMove<RegexNode>>();
		
		for (SFAInputMove<CharPred, Character> transition : aut.getInputMovesFrom(aut.getStates())) {
			CharPred guard = transition.guard;
			
			// Get intervals
			ImmutableList<ImmutablePair<Character, Character>> intervals = guard.intervals;
			
			// Make list of IntervalNodes
			List<IntervalNode> intervalNodeList = new ArrayList<IntervalNode>();
			
			for (ImmutablePair<Character, Character> interval : intervals) {
				NormalCharNode left = new NormalCharNode(interval.getLeft());
				NormalCharNode right = new NormalCharNode(interval.getRight());
				IntervalNode intervalNode = new IntervalNode(left, right);
				
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
				t.input.toString(regexString);
				
				sb.append(String.format("%s -> %s [label=\"%s\"]\n", t.from, t.to, regexString.toString()));
			}
		}
		sb.append("}");
		
		return sb.toString();
	}
	
	public static void main(String[] args) throws TimeoutException {
		// Test toSFARegex
		String CONFERENCE_NAME_REGEX = "[A-Z][a-z]*( [A-Z][a-z]*)*";
		SFA<CharPred, Character> CONFERENCE_NAME = (new SFAprovider(CONFERENCE_NAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		System.out.println(CONFERENCE_NAME.toDotString(ba));
		
		RegexFSA regexFSA = new RegexFSA(CONFERENCE_NAME);
		System.out.println(regexFSA.toDotString());
	}
	
}