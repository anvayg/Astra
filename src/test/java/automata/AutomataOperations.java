package automata;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;
import theory.characters.CharConstant;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import transducers.sft.SFTInputMove;
import transducers.sft.SFTMove;
import utilities.Pair;
import utilities.Triple;

public class AutomataOperations {
	
private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	private static SFA<CharPred, Character> mySFA01;
	private static SFA<CharPred, Character> mySFA02;
	private static SFA<CharPred, Character> mySFA03;
	private static SFA<CharPred, Character> mySFA04;
	private static SFA<CharPred, Character> mySFA09;
	private static SFA<CharPred, Character> mySFA11;
	
	private static SFT<CharPred, CharFunc, Character> mySFT01;
	
	public static void mkSFAs() throws TimeoutException {
		// SFA0.1: SFA that reads a
		List<SFAMove<CharPred, Character>> transitions01 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions01.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		List<Integer> finStates01 = new LinkedList<Integer>();
		finStates01.add(1);
		mySFA01 = SFA.MkSFA(transitions01, 0, finStates01, ba);
				
		// SFA0.2: SFA that reads b
		List<SFAMove<CharPred, Character>> transitions02 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions02.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('b')));
		List<Integer> finStates02 = new LinkedList<Integer>();
		finStates02.add(1);
		mySFA02 = SFA.MkSFA(transitions02, 0, finStates02, ba);
		mySFA03 = mySFA02.mkTotal(ba);
		
		// SFA0.4: SFA that reads ab(ab)*
		List<SFAMove<CharPred, Character>> transitions04 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions04.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions04.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('b')));
		transitions04.add(new SFAInputMove<CharPred, Character>(2, 1, new CharPred('a')));
		List<Integer> finStates04 = new LinkedList<Integer>();
		finStates04.add(2);
		mySFA04 = SFA.MkSFA(transitions04, 0, finStates04, ba);
		
		// SFA0.9: SFA that reads (;| (a|b);)*
		List<SFAMove<CharPred, Character>> transitions09 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions09.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred(';')));
		transitions09.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions09.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('b')));
		transitions09.add(new SFAInputMove<CharPred, Character>(1, 0, new CharPred(';')));
		List<Integer> finStates09 = new LinkedList<Integer>();
		finStates09.add(0);
		mySFA09 = SFA.MkSFA(transitions09, 0, finStates09, ba, false, false);
		
		// SFA1.1: SFA that reads (a*<s(c|t)a)*
		List<SFAMove<CharPred, Character>> transitions11 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions11.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred('a')));
		transitions11.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('<')));
		transitions11.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('s')));
		transitions11.add(new SFAInputMove<CharPred, Character>(2, 3, new CharPred('c')));
		transitions11.add(new SFAInputMove<CharPred, Character>(3, 4, new CharPred('r')));
		transitions11.add(new SFAInputMove<CharPred, Character>(3, 4, new CharPred('t')));
		transitions11.add(new SFAInputMove<CharPred, Character>(4, 5, new CharPred('>')));
		transitions11.add(new SFAInputMove<CharPred, Character>(5, 0, new CharPred('a')));
		List<Integer> finStates11 = new LinkedList<Integer>();
		finStates11.add(0);
		mySFA11 = SFA.MkSFA(transitions11, 0, finStates11, ba, false, false);
	}
	
	public static void mkSFTs() throws TimeoutException {
		// SFT01
		List<SFTMove<CharPred, CharFunc, Character>> transitions01 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output011 = new ArrayList<CharFunc>();
		output011.add(new CharConstant('b'));
		transitions01.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('a'), output011));
		Map<Integer, Set<List<Character>>> finStatesAndTails01 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails01.put(0, new HashSet<List<Character>>());
		mySFT01 = SFT.MkSFT(transitions01, 0, finStatesAndTails01, ba);
		
		
	}
	
	public static void getSuccessorStateTest() throws TimeoutException {
		Integer nextState = SFAOperations.getSuccessorState(mySFA02, 0, 'b', ba);
		assertTrue(nextState == 1);
		
		nextState = SFAOperations.getSuccessorState(mySFA03, 1, 'c', ba);
		assertTrue(nextState == 2);
	}
	
	public static void mkTotalFiniteTest() throws TimeoutException {
		Set<Character> alphabetSet = SFAOperations.alphabetSet(mySFA01, ba);
		alphabetSet.addAll(SFAOperations.alphabetSet(mySFA02, ba));
		SFA<CharPred, Character> mySFA01Total = SFAOperations.mkTotalFinite(mySFA01, alphabetSet, ba);
		
		Integer nextState = SFAOperations.getSuccessorState(mySFA01Total, 0, 'b', ba);
		assertTrue(nextState == 2);
		
		nextState = SFAOperations.getSuccessorState(mySFA01Total, 1, 'a', ba);
		assertTrue(nextState == 2);
	}
	
	// TODO: test for positions
	public static void getPositionTest() throws TimeoutException {
		List<Integer> positions = SFAOperations.getPositionInStr(mySFA04, 1, "a", ba);
		assertTrue(positions.get(0) == 1);
		
		positions = SFAOperations.getPositionInStr(mySFA04, 1, "aba", ba);
		assertTrue(positions.get(1) == 3);
	}
	
	public static void getOutputTest() throws TimeoutException {
		String outputStr = SFTOperations.getOutputString(mySFT01, "a", ba);
		assertTrue(outputStr.equals("b"));
		
		outputStr = SFTOperations.getOutputString(mySFT01, "aa", ba);
		assertTrue(outputStr.equals("bb"));
	}
	
	public static void transformTest() throws TimeoutException {
		SFA<CharPred, Character> newSFA = SFAOperations.pseudoNormalize(mySFA11, ba);
		System.out.println(newSFA.toDotString(ba));
	}
	
	public static void main(String[] args) throws TimeoutException {
		mkSFAs();
		mkSFTs();
		
		getSuccessorStateTest();
		mkTotalFiniteTest();
		getPositionTest();
		getOutputTest();
		transformTest();
		
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				 SFA.MkFiniteSFA(mySFA01, mySFA02, ba);
		System.out.println(triple.second.toDotString(ba));
	}
	
}
