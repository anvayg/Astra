package z3;

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
import solver.Constraints;
import solver.ConstraintsBV;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import utilities.Pair;

public class ConstraintsTestBV {

private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	private static SFA<CharPred, Character> mySFA01;
	private static SFA<CharPred, Character> mySFA02;
	private static SFA<CharPred, Character> mySFA03;
	private static SFA<CharPred, Character> mySFA07;
	private static SFA<CharPred, Character> mySFA08;
	
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
	}
	
	static SFT<CharPred, CharFunc, Character> customConstraintsTest(Context ctx, SFA<CharPred, Character> source, 
			SFA<CharPred, Character> target, int numStates, int outputBound, int[] fraction, 
			List<Pair<String, String>> ioExamples, SFA<CharPred, Character> template, String smtFile, boolean debug) throws TimeoutException {
		Set<Character> sourceAlphabetSet = SFAOperations.alphabetSet(source, ba);
		Set<Character> targetAlphabetSet = SFAOperations.alphabetSet(target, ba);
		Set<Character> alphabetSet = new HashSet<Character>();
		alphabetSet.addAll(sourceAlphabetSet);
		alphabetSet.addAll(targetAlphabetSet);
		
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		System.out.println(alphabetMap);
		
		// Make FAs total
		SFA<CharPred, Character> sourceTotal =  SFAOperations.mkTotalFinite(source, alphabetSet, ba);
		SFA<CharPred, Character> targetTotal = SFAOperations.mkTotalFinite(target, alphabetSet, ba);
		
		// Changed: not making source DFA total
		ConstraintsBV c = new ConstraintsBV(ctx, source, targetTotal, alphabetMap, ba);
		SFT<CharPred, CharFunc, Character> mySFT = c.mkConstraints(numStates, outputBound, fraction, ioExamples, template, smtFile, debug);
		
		for (Pair<String, String> example : ioExamples) {
        	String exampleOutput = SFTOperations.getOutputString(mySFT, example.first, ba);
            assertTrue(exampleOutput.equals(example.second));
        }
		
		return mySFT;
	}
	
	static void constraintsTest1(Context ctx) throws TimeoutException {
        int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        SFT<CharPred, CharFunc, Character> synthSFT = customConstraintsTest(ctx, mySFA01, mySFA03, 1, 2, fraction, examples, null, null, false);
        System.out.println(synthSFT.toDotString(ba));
	}
	
	static void constraintsTest2(Context ctx) throws TimeoutException {
        int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>(";", ";")); 
        examples.add(new Pair<String, String>("a;", "b;"));
        examples.add(new Pair<String, String>("b;", "b;"));
        SFT<CharPred, CharFunc, Character> synthSFT = customConstraintsTest(ctx, mySFA07, mySFA08, 2, 2, fraction, examples, null, null, false);
        System.out.println(synthSFT.toDotString(ba));
	}
	
	
	public static void main(String[] args) throws TimeoutException {
		HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        
        mkSFAs();
        
        constraintsTest1(ctx);
        // constraintsTest2(ctx);
	}
}
