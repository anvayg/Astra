package z3;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.Context;

import automata.SFAOperations;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;
import solver.Constraints;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import utilities.Pair;

public class ConstraintsTest {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	private static SFA<CharPred, Character> mySFA01;
	private static SFA<CharPred, Character> mySFA02;
	private static SFA<CharPred, Character> mySFA03;
	private static SFA<CharPred, Character> mySFA04;
	private static SFA<CharPred, Character> mySFA05;
	
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
		
		// SFA0.3: SFA that reads aa
		List<SFAMove<CharPred, Character>> transitions03 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions03.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions03.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('a')));
		List<Integer> finStates03 = new LinkedList<Integer>();
		finStates03.add(2);
		mySFA03 = SFA.MkSFA(transitions03, 0, finStates03, ba);
		
		// SFA0.4: SFA that reads bc
		List<SFAMove<CharPred, Character>> transitions04 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions04.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('b')));
		transitions04.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('c')));
		List<Integer> finStates04 = new LinkedList<Integer>();
		finStates04.add(2);
		mySFA04 = SFA.MkSFA(transitions04, 0, finStates04, ba);
		
		// SFA0.5: SFA that reads a(a|c)c*
		List<SFAMove<CharPred, Character>> transitions05 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions05.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions05.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('a')));
		transitions05.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('c')));
		transitions05.add(new SFAInputMove<CharPred, Character>(2, 2, new CharPred('c')));
		List<Integer> finStates05 = new LinkedList<Integer>();
		finStates05.add(2);
		mySFA05 = SFA.MkSFA(transitions05, 0, finStates05, ba, false, false); // important to prevent normalization and keep transitions in the same shape
	}
	
	static void constraintsTest(Context ctx) throws TimeoutException {
		// Make object
		Set<Character> alphabetSet = SFAOperations.alphabetSet(mySFA01, mySFA02, ba);
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		int numStates = 2;
		
		// Make FAs total
		SFA<CharPred, Character> mySFA01Total = SFAOperations.mkTotalFinite(mySFA01, alphabetSet, ba);
		SFA<CharPred, Character> mySFA02Total = SFAOperations.mkTotalFinite(mySFA02, alphabetSet, ba);
		
		// System.out.println(alphabetMap);
		Constraints c = new Constraints(ctx, mySFA01Total, mySFA02Total, alphabetMap, ba);
		int[] fraction = new int[] {1, 1};
		List<Pair<String, String>> empty = new ArrayList<Pair<String, String>>();
		SFT<CharPred, CharFunc, Character> mySFT = c.mkConstraints(numStates, 2, empty, fraction, false);
		System.out.println(mySFT.toDotString(ba));
	}
	
	static void constraintsTest2(Context ctx) throws TimeoutException {
		// Make object
		Set<Character> alphabetSet = SFAOperations.alphabetSet(mySFA03, mySFA04, ba);
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		int numStates = 3;
				
		// Make FAs total
		SFA<CharPred, Character> mySFA03Total = SFAOperations.mkTotalFinite(mySFA03, alphabetSet, ba);
		SFA<CharPred, Character> mySFA04Total = SFAOperations.mkTotalFinite(mySFA04, alphabetSet, ba);
				
		// System.out.println(alphabetMap);
		Constraints c = new Constraints(ctx, mySFA03Total, mySFA04Total, alphabetMap, ba);
		List<Pair<String, String>> empty = new ArrayList<Pair<String, String>>();
		int[] fraction = new int[] {1, 1};
		SFT<CharPred, CharFunc, Character> mySFT = c.mkConstraints(numStates, 2, empty, fraction, false);
		System.out.println(mySFT.toDotString(ba));
	}
	
	static void constraintsTest3(Context ctx) throws TimeoutException {
		// Make object
		Set<Character> alphabetSet = SFAOperations.alphabetSet(mySFA03, mySFA05, ba);
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		int numStates = 3;
				
		// Make FAs total
		SFA<CharPred, Character> mySFA03Total = SFAOperations.mkTotalFinite(mySFA03, alphabetSet, ba);
		SFA<CharPred, Character> mySFA05Total = SFAOperations.mkTotalFinite(mySFA05, alphabetSet, ba);
		
		Constraints c = new Constraints(ctx, mySFA03Total, mySFA05Total, alphabetMap, ba);
		List<Pair<String, String>> empty = new ArrayList<Pair<String, String>>();
		int[] fraction = new int[] {1, 1};
		SFT<CharPred, CharFunc, Character> mySFT = c.mkConstraints(numStates, 3, empty, fraction, true);
		System.out.println(mySFT.toDotString(ba));
	}
	
	
	public static void main(String[] args) throws TimeoutException {
		HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        
        mkSFAs();
        
        // constraintsTest(ctx);
        // constraintsTest2(ctx);
        constraintsTest3(ctx);
	}
	
}
