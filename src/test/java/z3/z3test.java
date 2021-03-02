package z3;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.junit.BeforeClass;
import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.BitVecSort;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import utilities.Pair;
import solver.Constraints;
import solver.ConstraintsEpsilon;

public class Z3test {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	private static SFA<CharPred, Character> mySFA01;
	private static SFA<CharPred, Character> mySFA02;
	private static SFA<CharPred, Character> mySFA03;
	private static SFA<CharPred, Character> mySFA04;
	
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
		// mySFA02 = mySFA02.mkTotal(ba);
		
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
		
		/* make alphabet: ad_hoc and using '0' as epsilon */
		HashMap<Character, Integer> alphabetMap = new HashMap<Character, Integer>();
		alphabetMap.put('a', 0);
		alphabetMap.put('b', 1);
		alphabetMap.put('0', 2);
		
		int numStates = 2;
		
		List<Pair<String, String>> empty = new ArrayList<Pair<String, String>>();
		solver = ConstraintsEpsilon.mkConstraints(ctx, solver, alphabetMap, mySFA01, mySFA02, 
				numStates, empty, ba);
	}
	
	public static void main(String[] args) throws TimeoutException {
		HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        
        mkSFAs();
        
        logicExample(ctx);
        constraintsTest(ctx);
	}
	
}
