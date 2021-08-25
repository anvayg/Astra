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

import SFT.GetTag;
import automata.SFAOperations;
import automata.SFTOperations;
import automata.fsa.FSA;
import automata.fst.FST;
import automata.fst.FSTLookahead;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;
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
		SFT<CharPred, CharFunc, Character> mySFT = c.mkConstraints(numStates, outputBound, fraction, ioExamples, template, null, smtFile, debug).first;
		
		for (Pair<String, String> example : ioExamples) {
        	String exampleOutput = SFTOperations.getOutputString(mySFT, example.first, ba);
            assertTrue(exampleOutput.equals(example.second));
        }
		
		return mySFT;
	}
	
	static SFT<CharPred, CharFunc, Character> customConstraintsTest2(Context ctx, SFA<CharPred, Character> source, 
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
		ConstraintsSolver c = new ConstraintsSolver(ctx, source, targetTotal, alphabetMap, numStates, outputBound, ioExamples, fraction, template, null, null, ba);
		SFT<CharPred, CharFunc, Character> mySFT = c.mkConstraints(smtFile, debug).first;
		
		for (Pair<String, String> example : ioExamples) {
        	String exampleOutput = SFTOperations.getOutputString(mySFT, example.first, ba);
            assertTrue(exampleOutput.equals(example.second));
        }
		
		return mySFT;
	}
	
	static FST<Pair<Character, Integer>, Character> customLookaheadConstraintsTest(Context ctx, 
			SFA<CharPred, Character> source, SFA<CharPred, Character> target, int numStates, int numLookaheadStates,
			int outputBound, int[] fraction, List<Pair<String, String>> ioExamples, SFA<CharPred, Character> template, 
			String smtFile, boolean debug) throws TimeoutException {
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
		
		// Calling LookaheadSolver
		ConstraintsSolverLookahead c = new ConstraintsSolverLookahead(ctx, source, targetTotal, alphabetMap, 
				numStates, numLookaheadStates, outputBound, ioExamples, fraction, template, null, null, ba);
		FSTLookahead<Character, Character> res = c.mkConstraints(smtFile, debug).first;
		FST<Pair<Character, Integer>, Character> lookaheadFT = res.getTransducer();
		FSA<Character> lookaheadAut = res.getAutomaton();
		
		for (Pair<String, String> example : ioExamples) {
        	List<Character> exampleOutput = res.outputOn(lOfS(example.first));
            assertTrue(exampleOutput.equals(lOfS(example.second)));
        }
		
		return lookaheadFT;
	}
	
	static void constraintsTest1(Context ctx) throws TimeoutException {
        int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        SFT<CharPred, CharFunc, Character> synthSFT = customConstraintsTest2(ctx, mySFA01, mySFA03, 1, 2, fraction, examples, null, null, false);
        System.out.println(synthSFT.toDotString(ba));
	}
	
	static void constraintsTest2(Context ctx) throws TimeoutException {
        int[] fraction = new int[] {1, 2};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>(";", ";")); 
        examples.add(new Pair<String, String>("a;", "b;"));
        examples.add(new Pair<String, String>("b;", "b;"));
        SFT<CharPred, CharFunc, Character> synthSFT = customConstraintsTest2(ctx, mySFA07, mySFA08, 1, 2, fraction, examples, null, null, false);
        System.out.println(synthSFT.toDotString(ba));
	}
	
	
	static void constraintsTest3(Context ctx) throws TimeoutException {
        int[] fraction = new int[] {1, 2};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>(";", ";")); 
        examples.add(new Pair<String, String>("a;", "b;"));
        examples.add(new Pair<String, String>("b;", "b;"));
        FST<Pair<Character, Integer>, Character> synthSFT = customLookaheadConstraintsTest(ctx, mySFA07, mySFA08, 1, 2, 2, fraction, examples, null, null, true);
        System.out.println(synthSFT.toDotString());
	}
	
	
	static void getTags(Context ctx) throws TimeoutException {
		SFT<CharPred, CharFunc, Character> GetTags = GetTag.MkGetTagsSFT();
		System.out.println(GetTags.toDotString(ba));
		
		SFA<CharPred, Character> source = GetTags.getDomain(ba).removeEpsilonMoves(ba).determinize(ba);
		System.out.println(source.toDotString(ba));
		
		assertTrue(source.accepts(lOfS("<<s<"), ba));
		assertTrue(source.accepts(lOfS("<<s<s>"), ba));
		assertTrue(source.accepts(lOfS("<<s<st"), ba));
		System.out.println(source.toDotString(ba));
	
		SFA<CharPred, Character> target = GetTags.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		System.out.println(target.toDotString(ba));
		
		int[] fraction = new int[] {2, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("<<s<", ""));
		examples.add(new Pair<String, String>("<st", ""));
		examples.add(new Pair<String, String>("<s>", "<s>"));
		examples.add(new Pair<String, String>("<st<s>", "<s>"));
		SFT<CharPred, CharFunc, Character> synthSFT = 
				ConstraintsTestSymbolic.customLookaheadConstraintsTest(source, target, 2, 2, 2, fraction, examples, null, "getTags.smt2", true);
				// ConstraintsTestSymbolic.customConstraintsTest(source, target, 4, 2, fraction, examples, source, true);
		
	}
	
	private static List<Character> lOfS(String s) {
		List<Character> l = new ArrayList<Character>();
		char[] ca = s.toCharArray();
		for (int i = 0; i < s.length(); i++)
			l.add(ca[i]);
		return l;
	}
	
	public static void main(String[] args) throws TimeoutException {
		HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        
        mkSFAs();
        
        // constraintsTest1(ctx);
        // constraintsTest2(ctx);
        // constraintsTest3(ctx);
        getTags(ctx);
	}
}
