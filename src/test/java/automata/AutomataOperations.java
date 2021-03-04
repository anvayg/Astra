package automata;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import utilities.Pair;
import utilities.Triple;

public class AutomataOperations {
	
private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	private static SFA<CharPred, Character> mySFA01;
	private static SFA<CharPred, Character> mySFA02;
	private static SFA<CharPred, Character> mySFA03;
	
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
		
	}
	
	public static void getSuccessorStateTest() throws TimeoutException {
		Integer nextState = SFAOperations.getSuccessorState(mySFA02, 0, 'b', ba);
		assertTrue(nextState == 1);
		
		nextState = SFAOperations.getSuccessorState(mySFA03, 1, 'c', ba);
		assertTrue(nextState == 2);
	}
	
	public static void mkTotalFiniteTest() throws TimeoutException {
		Set<Character> alphabetSet = SFAOperations.alphabetSet(mySFA01, mySFA02, ba);
		SFA<CharPred, Character> mySFA01Total = SFAOperations.mkTotalFinite(mySFA01, alphabetSet, ba);
		
		Integer nextState = SFAOperations.getSuccessorState(mySFA01Total, 0, 'b', ba);
		assertTrue(nextState == 2);
		
		nextState = SFAOperations.getSuccessorState(mySFA01Total, 1, 'a', ba);
		assertTrue(nextState == 2);
	}
	
	
	public static void main(String[] args) throws TimeoutException {
		mkSFAs();
		
		getSuccessorStateTest();
		mkTotalFiniteTest();
		
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				 SFA.MkFiniteSFA(mySFA01, mySFA02, ba);
		System.out.println(triple.second.toDotString(ba));
		
		HashSet<Character> alphabet = SFAOperations.alphabetSet(mySFA01, mySFA02, ba);
		System.out.println(alphabet.toString());
	}
	
}
