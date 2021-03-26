package z3;


import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.junit.BeforeClass;
import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.BitVecSort;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

import automata.SFAOperations;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import utilities.Pair;
import utilities.Triple;
import solver.ConstraintsFixedOutputs;
import strings.EditDistanceStrToStr;

public class ConstraintsFOTest {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	private static SFA<CharPred, Character> mySFA01;
	private static SFA<CharPred, Character> mySFA02;
	private static SFA<CharPred, Character> mySFA03;
	private static SFA<CharPred, Character> mySFA04;
	private static SFA<CharPred, Character> mySFA05;
	private static SFA<CharPred, Character> mySFA06;
	
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
				
		// SFA0.4: SFA that reads ab
		List<SFAMove<CharPred, Character>> transitions04 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions04.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions04.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('b')));
		List<Integer> finStates04 = new LinkedList<Integer>();
		finStates04.add(2);
		mySFA04 = SFA.MkSFA(transitions04, 0, finStates04, ba);
		
		// SFA0.5: SFA that reads ac(a|c)c*
		List<SFAMove<CharPred, Character>> transitions05 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions05.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions05.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('c')));
		transitions05.add(new SFAInputMove<CharPred, Character>(2, 3, new CharPred('a')));
		transitions05.add(new SFAInputMove<CharPred, Character>(2, 3, new CharPred('c')));
		transitions05.add(new SFAInputMove<CharPred, Character>(3, 3, new CharPred('c')));
		List<Integer> finStates05 = new LinkedList<Integer>();
		finStates05.add(3);
		mySFA05 = SFA.MkSFA(transitions05, 0, finStates05, ba);
		
		// SFA0.6: SFA that reads ab(ab)*
		List<SFAMove<CharPred, Character>> transitions06 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions06.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions06.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('b')));
		transitions06.add(new SFAInputMove<CharPred, Character>(2, 1, new CharPred('a')));
		List<Integer> finStates06 = new LinkedList<Integer>();
		finStates06.add(2);
		mySFA06 = SFA.MkSFA(transitions06, 0, finStates06, ba);
	}
	
	/**
	 * z3 test borrowed from JavaExample
	 * 
	 */
	static void logicExample(Context ctx) {
		System.out.println("LogicTest");
		
		BitVecSort bvs = ctx.mkBitVecSort(32);
        Expr x = ctx.mkConst("x", bvs);
        Expr y = ctx.mkConst("y", bvs);
        BoolExpr eq = ctx.mkEq(x, y);
        
        // Use a solver for QF_BV
        Solver s = ctx.mkSolver("QF_BV");
        s.add(eq);
        Status res = s.check();
        System.out.println("solver result: " + res);
	}
	
	static void constraintsTest(Context ctx) throws TimeoutException {
		Solver solver = ctx.mkSolver();
		
		Set<Character> alphabetSet = SFAOperations.alphabetSet(mySFA01, mySFA02, ba);
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		SFA<CharPred, Character> mySFA02Total = SFAOperations.mkTotalFinite(mySFA02, alphabetSet, ba);
		int numStates = 2;
		
		List<Pair<String, String>> empty = new ArrayList<Pair<String, String>>();
		SFT<CharPred, CharFunc, Character> mySFT = ConstraintsFixedOutputs.mkConstraints(ctx, solver, alphabetMap, mySFA01, mySFA02Total, 
				numStates, empty, ba, false);
		SFA<CharPred, Character> outputLang = mySFT.getOverapproxOutputSFA(ba);
		assertTrue(outputLang.includedIn(mySFA02Total, ba));
	}
	
	static void constraintsTest2(Context ctx) throws TimeoutException {
		Solver solver = ctx.mkSolver();
		
		Set<Character> alphabetSet = SFAOperations.alphabetSet(mySFA03, mySFA04, ba);
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		SFA<CharPred, Character> mySFA04Total = SFAOperations.mkTotalFinite(mySFA04, alphabetSet, ba);
		int numStates = 3;
		
		List<Pair<String, String>> empty = new ArrayList<Pair<String, String>>();
		SFT<CharPred, CharFunc, Character> mySFT = ConstraintsFixedOutputs.mkConstraints(ctx, solver, alphabetMap, mySFA03, mySFA04Total, 
				numStates, empty, ba, false);
		SFA<CharPred, Character> outputLang = mySFT.getOverapproxOutputSFA(ba);
		assertTrue(outputLang.includedIn(mySFA04Total, ba));
	}
	
	static void constraintsExampleTest(Context ctx) throws TimeoutException {
		Solver solver = ctx.mkSolver();
		
		Set<Character> alphabetSet = SFAOperations.alphabetSet(mySFA01, mySFA02, ba);
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		SFA<CharPred, Character> mySFA02Total = SFAOperations.mkTotalFinite(mySFA02, alphabetSet, ba);
		int numStates = 2;
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("a", "b"));
		SFT<CharPred, CharFunc, Character> mySFT = ConstraintsFixedOutputs.mkConstraints(ctx, solver, alphabetMap, mySFA01, mySFA02Total, 
				numStates, examples, ba, false);
		SFA<CharPred, Character> outputLang = mySFT.getOverapproxOutputSFA(ba);
		assertTrue(outputLang.includedIn(mySFA02Total, ba));
	}
	
	static void constraintsExampleTest2(Context ctx) throws TimeoutException {
		Solver solver = ctx.mkSolver();
		
		Set<Character> alphabetSet = SFAOperations.alphabetSet(mySFA03, mySFA04, ba);
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		SFA<CharPred, Character> mySFA04Total = SFAOperations.mkTotalFinite(mySFA04, alphabetSet, ba);
		int numStates = 3;
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("aa", "ab"));
		SFT<CharPred, CharFunc, Character> mySFT = ConstraintsFixedOutputs.mkConstraints(ctx, solver, alphabetMap, mySFA03, mySFA04Total, 
				numStates, examples, ba, false);
		// System.out.println(mySFT.toDotString(ba));
		SFA<CharPred, Character> outputLang = mySFT.getOverapproxOutputSFA(ba);
		assertTrue(outputLang.includedIn(mySFA04Total, ba));
	}
	
	static void constraintsExampleTest3(Context ctx) throws TimeoutException {
		Solver solver = ctx.mkSolver();
		
		Set<Character> alphabetSet = SFAOperations.alphabetSet(mySFA04, mySFA06, ba);
		// System.out.println(alphabetSet);
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		// System.out.println(alphabetMap);
		SFA<CharPred, Character> mySFA06Total = SFAOperations.mkTotalFinite(mySFA06, alphabetSet, ba);
		int numStates = 3;
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("ab", "abab"));
		SFT<CharPred, CharFunc, Character> mySFT = ConstraintsFixedOutputs.mkConstraints(ctx, solver, alphabetMap, mySFA04, mySFA06Total, 
				numStates, examples, ba, false);
		SFA<CharPred, Character> outputLang = mySFT.getOverapproxOutputSFA(ba);
		assertTrue(outputLang.includedIn(mySFA06Total, ba));
	}
	
	static void constraintsExampleTest4(Context ctx) throws TimeoutException {
		Solver solver = ctx.mkSolver();
		
		Set<Character> alphabetSet = SFAOperations.alphabetSet(mySFA04, mySFA05, ba);
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		SFA<CharPred, Character> mySFA05Total = SFAOperations.mkTotalFinite(mySFA05, alphabetSet, ba);
		int numStates = 3;
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("ab", "accc"));
		SFT<CharPred, CharFunc, Character> mySFT = ConstraintsFixedOutputs.mkConstraints(ctx, solver, alphabetMap, mySFA04, mySFA05Total, 
				numStates, examples, ba, false);
		SFA<CharPred, Character> outputLang = mySFT.getOverapproxOutputSFA(ba);
		assertTrue(outputLang.includedIn(mySFA05Total, ba));
	}
	
	static void exampleTransitionsTest() throws TimeoutException {
		Set<Character> alphabetSet = SFAOperations.alphabetSet(mySFA01, mySFA05, ba);
		SFA<CharPred, Character> mySFA05Total = SFAOperations.mkTotalFinite(mySFA05, alphabetSet, ba);
		
		Pair<String, String> example = new Pair<String, String>("a", "ac");
		Set<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> transitions = 
				ConstraintsFixedOutputs.bestOutputsExamples(mySFA01, mySFA05Total, example, ba);
		// System.out.println(transitions);
		
		
		alphabetSet = SFAOperations.alphabetSet(mySFA04, mySFA06, ba);
		SFA<CharPred, Character> mySFA06Total = SFAOperations.mkTotalFinite(mySFA06, alphabetSet, ba);
		example = new Pair<String, String>("ab", "abab");
		transitions = ConstraintsFixedOutputs.bestOutputsExamples(mySFA04, mySFA06Total, example, ba);
		// System.out.println(transitions);
	}
	
	public static void main(String[] args) throws TimeoutException {
		HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        
        mkSFAs();
        
        logicExample(ctx);
        constraintsTest(ctx);
        constraintsTest2(ctx);
        constraintsExampleTest(ctx);
        constraintsExampleTest2(ctx);
        constraintsExampleTest3(ctx);
        constraintsExampleTest4(ctx);
        exampleTransitionsTest();
	}
	
}
