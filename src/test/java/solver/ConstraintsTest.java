package solver;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.Context;

import automata.SFAOperations;
import automata.SFTOperations;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;
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
	private static SFA<CharPred, Character> mySFA06;
	private static SFA<CharPred, Character> mySFA07;
	private static SFA<CharPred, Character> mySFA08;
	private static SFA<CharPred, Character> mySFA09;
	private static SFA<CharPred, Character> mySFA10;
	private static SFA<CharPred, Character> mySFA11;
	private static SFA<CharPred, Character> mySFA12;
	private static SFA<CharPred, Character> mySFA13;
	private static SFA<CharPred, Character> mySFA14;
	
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
		
		// SFA0.3: SFA that reads ab
		List<SFAMove<CharPred, Character>> transitions03 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions03.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions03.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('b')));
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
	
		// SFA0.6: SFA that reads ab+a
		List<SFAMove<CharPred, Character>> transitions06 = new LinkedList<SFAMove<CharPred, Character>>();
		// transitions06.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions06.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('b')));
		transitions06.add(new SFAInputMove<CharPred, Character>(2, 2, new CharPred('b')));
		transitions06.add(new SFAInputMove<CharPred, Character>(2, 3, new CharPred('a')));
		List<Integer> finStates06 = new LinkedList<Integer>();
		finStates06.add(3);
		mySFA06 = SFA.MkSFA(transitions06, 0, finStates06, ba, false, false);
		
		// SFA0.7: SFA that reads (;| (a|b);)
		List<SFAMove<CharPred, Character>> transitions07 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions07.add(new SFAInputMove<CharPred, Character>(0, 3, new CharPred(';')));
		transitions07.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		// transitions07.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('a')));
		transitions07.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('b')));
		transitions07.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred(';')));
		List<Integer> finStates07 = new LinkedList<Integer>();
		finStates07.add(3);
		finStates07.add(2);
		mySFA07 = SFA.MkSFA(transitions07, 0, finStates07, ba, false, false);
		
		// SFA0.8: SFA that reads (; | b;)
		List<SFAMove<CharPred, Character>> transitions08 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions08.add(new SFAInputMove<CharPred, Character>(0, 3, new CharPred(';')));
		transitions08.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('b')));
		// transitions08.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('a')));
		transitions08.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred(';')));
		List<Integer> finStates08 = new LinkedList<Integer>();
		finStates08.add(3);
		finStates08.add(2);
		mySFA08 = SFA.MkSFA(transitions08, 0, finStates08, ba, false, false);
		
		// SFA0.9: SFA that reads (;| (a|b);)*
		List<SFAMove<CharPred, Character>> transitions09 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions09.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred(';')));
		transitions09.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions09.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('b')));
		transitions09.add(new SFAInputMove<CharPred, Character>(1, 0, new CharPred(';')));
		List<Integer> finStates09 = new LinkedList<Integer>();
		finStates09.add(0);
		mySFA09 = SFA.MkSFA(transitions09, 0, finStates09, ba, false, false);
		
		// SFA1.0: SFA that reads (;| a;)*
		List<SFAMove<CharPred, Character>> transitions10 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions10.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred(';')));
		transitions10.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions10.add(new SFAInputMove<CharPred, Character>(1, 0, new CharPred(';')));
		List<Integer> finStates10 = new LinkedList<Integer>();
		finStates10.add(0);
		mySFA10 = SFA.MkSFA(transitions10, 0, finStates10, ba, false, false);
		
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
		
		// SFA1.2: SFA that reads a*
		List<SFAMove<CharPred, Character>> transitions12 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions12.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred('a')));
		transitions12.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred('<')));
		transitions12.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred('s')));
		transitions12.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred('c')));
		transitions12.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred('r')));
		transitions12.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred('t')));
		transitions12.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred('>')));
		List<Integer> finStates12 = new LinkedList<Integer>();
		finStates12.add(0);
		mySFA12 = SFA.MkSFA(transitions12, 0, finStates12, ba, false, false);
		
		// SFA1.3: a^4(a|b) (big input language)
		List<SFAMove<CharPred, Character>> transitions13 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions13.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions13.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('a')));
		transitions13.add(new SFAInputMove<CharPred, Character>(2, 3, new CharPred('a')));
		transitions13.add(new SFAInputMove<CharPred, Character>(3, 4, new CharPred('a')));
		transitions13.add(new SFAInputMove<CharPred, Character>(4, 5, new CharPred('a')));
		transitions13.add(new SFAInputMove<CharPred, Character>(4, 5, new CharPred('b')));
		List<Integer> finStates13 = new LinkedList<Integer>();
		finStates13.add(5);
		mySFA13 = SFA.MkSFA(transitions13, 0, finStates13, ba, false, false);
		
		// SFA1.4: 
		List<SFAMove<CharPred, Character>> transitions14 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions14.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred('a')));
		transitions14.add(new SFAInputMove<CharPred, Character>(0, 0, new CharPred('b')));
		List<Integer> finStates14 = new LinkedList<Integer>();
		finStates14.add(0);
		mySFA14 = SFA.MkSFA(transitions14, 0, finStates14, ba, false, false);
	}
	
	static SFT<CharPred, CharFunc, Character> customConstraintsTest(Context ctx, SFA<CharPred, Character> source, 
			SFA<CharPred, Character> target, int numStates, int outputBound, int[] fraction, 
			List<Pair<String, String>> ioExamples, SFA<CharPred, Character> template, 
			String encoding, String smtFile, boolean debug) throws TimeoutException {
		Set<Character> sourceAlphabetSet = SFAOperations.alphabetSet(source, ba);
		Set<Character> targetAlphabetSet = SFAOperations.alphabetSet(target, ba);
		Set<Character> alphabetSet = new HashSet<Character>();
		alphabetSet.addAll(sourceAlphabetSet);
		alphabetSet.addAll(targetAlphabetSet);
		
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		System.out.println(alphabetMap);
		
		// Make FAs total: Changed, not making source DFA total
		SFA<CharPred, Character> targetTotal = SFAOperations.mkTotalFinite(target, alphabetSet, ba);
		
		SFT<CharPred, CharFunc, Character> mySFT = null;
		if (encoding.equals("int")) {
			Constraints c = new Constraints(ctx, source, targetTotal, alphabetMap, ba);
			mySFT = c.mkConstraints(numStates, outputBound, fraction, ioExamples, template, null, smtFile, debug);
		} else if (encoding.equals("bitvec")) {
			ConstraintsBV c = new ConstraintsBV(ctx, source, targetTotal, alphabetMap, ba);
			mySFT = c.mkConstraints(numStates, outputBound, fraction, ioExamples, template, null, smtFile, debug).first;
		} else {
			throw new IllegalArgumentException("Invalid encoding string");
		}
		
		for (Pair<String, String> example : ioExamples) {
        	String exampleOutput = SFTOperations.getOutputString(mySFT, example.first, ba);
            assertTrue(exampleOutput.equals(example.second));
        }
		
		return mySFT;
	}
	
	// see if a --> ab works
	static void constraintsTest(Context ctx) throws TimeoutException {
		// Make object
		Set<Character> sourceAlphabetSet = SFAOperations.alphabetSet(mySFA01, ba);
		Set<Character> targetAlphabetSet = SFAOperations.alphabetSet(mySFA03, ba);
		Set<Character> alphabetSet = new HashSet<Character>();
		alphabetSet.addAll(sourceAlphabetSet);
		alphabetSet.addAll(targetAlphabetSet);
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		int numStates = 2;
		
		// Make FAs total
		SFA<CharPred, Character> mySFA01Total = SFAOperations.mkTotalFinite(mySFA01, alphabetSet, ba);
		SFA<CharPred, Character> mySFA03Total = SFAOperations.mkTotalFinite(mySFA03, alphabetSet, ba);
		
		// System.out.println(alphabetMap);
		Constraints c = new Constraints(ctx, mySFA01Total, mySFA03Total, alphabetMap, ba);
		int[] fraction = new int[] {1, 1};
		List<Pair<String, String>> empty = new ArrayList<Pair<String, String>>();
		SFT<CharPred, CharFunc, Character> mySFT = c.mkConstraints(numStates, 2, fraction, empty, true);
		System.out.println(mySFT.toDotString(ba));
	}
	
	static void constraintsTest2(Context ctx) throws TimeoutException {
		// Make object
		Set<Character> sourceAlphabetSet = SFAOperations.alphabetSet(mySFA03, ba);
		Set<Character> targetAlphabetSet = SFAOperations.alphabetSet(mySFA04, ba);
		Set<Character> alphabetSet = new HashSet<Character>();
		alphabetSet.addAll(sourceAlphabetSet);
		alphabetSet.addAll(targetAlphabetSet);
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		int numStates = 1;
				
		// Make FAs total
		SFA<CharPred, Character> mySFA03Total = SFAOperations.mkTotalFinite(mySFA03, alphabetSet, ba);
		SFA<CharPred, Character> mySFA04Total = SFAOperations.mkTotalFinite(mySFA04, alphabetSet, ba);
				
		// System.out.println(alphabetMap);
		Constraints c = new Constraints(ctx, mySFA03Total, mySFA04Total, alphabetMap, ba);
		List<Pair<String, String>> empty = new ArrayList<Pair<String, String>>();
		int[] fraction = new int[] {1, 1};
		SFT<CharPred, CharFunc, Character> mySFT = c.mkConstraints(numStates, 2, fraction, empty, false);
		System.out.println(mySFT.toDotString(ba));
	}
	
	/* language to language test from infinite set to infinite set */
	static void constraintsTest4(Context ctx) throws TimeoutException {
		Set<Character> sourceAlphabetSet = SFAOperations.alphabetSet(mySFA05, ba);
		Set<Character> targetAlphabetSet = SFAOperations.alphabetSet(mySFA06, ba);
		Set<Character> alphabetSet = new HashSet<Character>();
		alphabetSet.addAll(sourceAlphabetSet);
		alphabetSet.addAll(targetAlphabetSet);
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		int numStates = 3;
		
		// Make FAs total
		SFA<CharPred, Character> mySFA05Total = SFAOperations.mkTotalFinite(mySFA05, alphabetSet, ba);
		SFA<CharPred, Character> mySFA06Total = SFAOperations.mkTotalFinite(mySFA06, alphabetSet, ba);
		
		Constraints c = new Constraints(ctx, mySFA05Total, mySFA06Total, alphabetMap, ba);
		int[] fraction = new int[] {1, 1};
		SFT<CharPred, CharFunc, Character> mySFT = c.mkConstraints(numStates, 3, fraction, true);
		System.out.println(mySFT.toDotString(ba));
	}
	
	static void constraintsTest5(Context ctx) throws TimeoutException {
        int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>(";", ";")); 
        examples.add(new Pair<String, String>("a;", "b;"));
        examples.add(new Pair<String, String>("b;", "b;"));
        SFT<CharPred, CharFunc, Character> synthSFT = customConstraintsTest(ctx, mySFA07, mySFA08, 1, 2, fraction, examples, null, "bitvec", "test5.smt2", false);
        System.out.println(synthSFT.toDotString(ba));
	}
	
	static void constraintsTest6(Context ctx) throws TimeoutException {
        int[] fraction = new int[] {1, 2};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        
        examples.add(new Pair<String, String>("b;", ";"));
        examples.add(new Pair<String, String>("a;", "a;")); 
        examples.add(new Pair<String, String>(";", ";"));
        SFT<CharPred, CharFunc, Character> synthSFT = customConstraintsTest(ctx, mySFA09, mySFA10, 3, 2, fraction, examples, null, "int", null, false);
        System.out.println(synthSFT.toDotString(ba));
        
        String exampleOutput1 = SFTOperations.getOutputString(synthSFT, "b;", ba);
        assertTrue(exampleOutput1.equals(";"));
        
        String exampleOutput2 = SFTOperations.getOutputString(synthSFT, "a;", ba);
        assertTrue(exampleOutput2.equals("a;"));
	}
	
	static void constraintsTest7(Context ctx) throws TimeoutException {
        int[] fraction = new int[] {2, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("a<scr>a", "aa"));
        examples.add(new Pair<String, String>("a<sct>a", "a<sct>a"));
        
        // SFA<CharPred, Character> template = SFAOperations.pseudoNormalize(mySFA11, ba);
        SFA<CharPred, Character> template = mySFA11;
        System.out.println(template.toDotString(ba));
        
        SFT<CharPred, CharFunc, Character> synthSFT = customConstraintsTest(ctx, mySFA11, mySFA12, template.stateCount(), 5, fraction, examples, template, "bitvec", "test7.smt2", false);
        System.out.println(synthSFT.toDotString(ba));
	}
	
	static void constraintsTest8(Context ctx) throws TimeoutException {
        int[] fraction = new int[] {2, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("aaaab", ""));
        examples.add(new Pair<String, String>("aaaaa", "aaaaa"));
        SFT<CharPred, CharFunc, Character> synthSFT = customConstraintsTest(ctx, mySFA13, mySFA14, 5, 5, fraction, examples, null, "bitvec", null, false);
        System.out.println(synthSFT.toDotString(ba));
	}
	
	static void constraintsTest9(Context ctx) throws TimeoutException {
        int[] fraction = new int[] {2, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        SFT<CharPred, CharFunc, Character> synthSFT = customConstraintsTest(ctx, mySFA03, mySFA13, 2, 3, fraction, examples, null, "int", null, false);
        System.out.println(synthSFT.toDotString(ba));
	}
	
	public static void main(String[] args) throws TimeoutException {
		HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        
        mkSFAs();
        
        // constraintsTest(ctx);
        // constraintsTest2(ctx);
        // constraintsTest3(ctx);
        // constraintsTest4(ctx);
        // constraintsTest5(ctx);
        // constraintsTest6(ctx);
        constraintsTest7(ctx);
        // constraintsTest8(ctx);
        // constraintsTest9(ctx);
	}
	
}
