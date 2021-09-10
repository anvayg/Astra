package solver;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.Context;

import automata.SFAOperations;
import automata.SFTOperations;
import automata.fsa.FSA;
import automata.fst.FST;
import automata.fst.FSTLookahead;
import automata.fst.FSTOperations;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;
import theory.characters.CharConstant;
import theory.characters.CharFunc;
import theory.characters.CharOffset;
import theory.characters.CharPred;
import theory.characters.StdCharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import transducers.sft.SFTInputMove;
import transducers.sft.SFTMove;
import utilities.Pair;
import utilities.SFAprovider;
import utilities.Triple;

public class ConstraintsTestSymbolic {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	private static SFA<CharPred, Character> mySFA01;
	private static SFA<CharPred, Character> mySFA02;
	private static SFA<CharPred, Character> mySFA07;
	private static SFA<CharPred, Character> mySFA08;
	
	private static SFT<CharPred, CharFunc, Character> mySFT16;
	private static SFT<CharPred, CharFunc, Character> mySFT17;
	
	public static void mkSFAs() throws TimeoutException {
		String regex = "abc|de";
		SFAprovider test = new SFAprovider(regex, ba);
		SFA<CharPred, Character> sfa = test.getSFA();
		
		/* mySFA01 */
		String regex1 = "\\w<\\w*>\\w";
		SFAprovider test1 = new SFAprovider(regex1, ba);
		mySFA01 = (test1.getSFA()).removeEpsilonMoves(ba);
		
		/* mySFA02: ^(?!<scr>).*$ */
		List<SFAMove<CharPred, Character>> transitions02 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions02.add(new SFAInputMove<CharPred, Character>(0, 0, ba.MkNot(new CharPred('<')))); 
		transitions02.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('<')));
		transitions02.add(new SFAInputMove<CharPred, Character>(1, 0, ba.MkNot(new CharPred('s'))));
		transitions02.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('s')));
		transitions02.add(new SFAInputMove<CharPred, Character>(2, 0, ba.MkNot(new CharPred('c'))));
		transitions02.add(new SFAInputMove<CharPred, Character>(2, 3, new CharPred('c')));
		transitions02.add(new SFAInputMove<CharPred, Character>(3, 0, ba.MkNot(new CharPred('r'))));
		transitions02.add(new SFAInputMove<CharPred, Character>(3, 4, new CharPred('r')));
		transitions02.add(new SFAInputMove<CharPred, Character>(4, 0, ba.MkNot(new CharPred('>'))));
		transitions02.add(new SFAInputMove<CharPred, Character>(4, 5, new CharPred('>')));
		List<Integer> finStates02 = new LinkedList<Integer>();
		finStates02.add(0);
		mySFA02 = SFA.MkSFA(transitions02, 0, finStates02, ba);
		
		// DOS carriage return
		List<SFAMove<CharPred, Character>> transitions07 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions07.add(new SFAInputMove<CharPred, Character>(0, 0, StdCharPred.ALPHA));
		transitions07.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('\\')));
		transitions07.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('r')));
		transitions07.add(new SFAInputMove<CharPred, Character>(2, 3, new CharPred('\\')));
		transitions07.add(new SFAInputMove<CharPred, Character>(3, 0, new CharPred('n')));
		List<Integer> finStates07 = new LinkedList<Integer>();
		finStates07.add(0);
		mySFA07 = SFA.MkSFA(transitions07, 0, finStates07, ba);
				
		// Unix carriage return
		List<SFAMove<CharPred, Character>> transitions08 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions08.add(new SFAInputMove<CharPred, Character>(0, 0, StdCharPred.ALPHA));
		transitions08.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('\\')));
		transitions08.add(new SFAInputMove<CharPred, Character>(1, 0, new CharPred('n')));
		List<Integer> finStates08 = new LinkedList<Integer>();
		finStates08.add(0);
		mySFA08 = SFA.MkSFA(transitions08, 0, finStates08, ba);
		
		
		// SFT1.6: escapequotes_buggy
		// https://rise4fun.com/Bek/escapequotes_buggy
		List<SFTMove<CharPred, CharFunc, Character>> transitions16 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output161 = new ArrayList<CharFunc>();
		output161.add(CharOffset.IDENTITY);
		CharPred quotes = ba.MkOr(new CharPred('\''), new CharPred('\"'));
		CharPred backslash = new CharPred('\\');
		CharPred notQuotesAndBackslash = ba.MkAnd(ba.MkNot(quotes), ba.MkNot(backslash));
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, notQuotesAndBackslash, output161));
		List<CharFunc> output162 = new ArrayList<CharFunc>();
		output162.add(new CharConstant('\\'));
		output162.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, quotes, output162));
		List<CharFunc> output163 = new ArrayList<CharFunc>();
		output163.add(CharOffset.IDENTITY);
		output163.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, backslash, output163));
		List<CharFunc> output164 = new ArrayList<CharFunc>();
		output164.add(CharOffset.IDENTITY);
		output164.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, backslash, output164)); // bug here
		List<CharFunc> output165 = new ArrayList<CharFunc>();
		output165.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, ba.MkNot(backslash), output165));
		Map<Integer, Set<List<Character>>> finStatesAndTails16 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails16.put(0, new HashSet<List<Character>>());
		// finStatesAndTails16.put(1, new HashSet<List<Character>>());
		mySFT16 = SFT.MkSFT(transitions16, 0, finStatesAndTails16, ba);
				
		// SFT1.7: escapequotes_correct
		List<SFTMove<CharPred, CharFunc, Character>> transitions17 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output171 = new ArrayList<CharFunc>();
		output171.add(CharOffset.IDENTITY);
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, notQuotesAndBackslash, output171));
		List<CharFunc> output172 = new ArrayList<CharFunc>();
		output172.add(new CharConstant('\\'));
		output172.add(CharOffset.IDENTITY);
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, quotes, output172));
		List<CharFunc> output173 = new ArrayList<CharFunc>();
		output173.add(CharOffset.IDENTITY); // corrected
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, backslash, output173));
		List<CharFunc> output174 = new ArrayList<CharFunc>();
		output174.add(CharOffset.IDENTITY);
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, backslash, output174)); // corrected
		List<CharFunc> output175 = new ArrayList<CharFunc>();
		output175.add(CharOffset.IDENTITY);
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, ba.MkNot(backslash), output175));
		Map<Integer, Set<List<Character>>> finStatesAndTails17 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails17.put(0, new HashSet<List<Character>>());
		// finStatesAndTails17.put(1, new HashSet<List<Character>>());
		mySFT17 = SFT.MkSFT(transitions17, 0, finStatesAndTails17, ba);
	}
	
	/* convert example strings to their 'finite' versions using minterms */
	static List<Pair<String, String>> finitizeExamples(List<Pair<String, String>> ioExamples, 
			Map<CharPred, Pair<CharPred, ArrayList<Integer>>> minterms) throws TimeoutException {
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		
		for (Pair<String, String> example : ioExamples) {
			String input = SFAOperations.finitizeStringMinterms(example.first, minterms, ba);
			String output = SFAOperations.finitizeStringMinterms(example.second, minterms, ba);
			examples.add(new Pair<String, String>(input, output));
		}
		
		return examples;
	}
	
	/* testing function with examples as well */
	public static SFT<CharPred, CharFunc, Character> customConstraintsTest(SFA<CharPred, Character> source, 
			SFA<CharPred, Character> target, int numStates, int outputBound, int[] fraction, 
			List<Pair<String, String>> ioExamples, SFA<CharPred, Character> template, boolean debug) throws TimeoutException {
		HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
		
		// Make finite automata out of source and target
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(source, target, ba);
		
		System.out.println(source.toDotString(ba));
		System.out.println(target.toDotString(ba));
		SFA<CharPred, Character> sourceFinite = triple.first;
		SFA<CharPred, Character> targetFinite = triple.second;
		System.out.println(sourceFinite.toDotString(ba));
		System.out.println(targetFinite.toDotString(ba));
		
		Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterm = triple.third;
		
		List<Pair<String, String>> examplesFinite = finitizeExamples(ioExamples, idToMinterm);
		
		Set<Character> sourceAlphabetSet = SFAOperations.alphabetSet(sourceFinite, ba);
		Set<Character> targetAlphabetSet = SFAOperations.alphabetSet(targetFinite, ba);
		Set<Character> alphabetSet = new HashSet<Character>();
		alphabetSet.addAll(sourceAlphabetSet);
		alphabetSet.addAll(targetAlphabetSet);
		
//		System.out.println(SFAOperations.getStateInFA(source, source.getInitialState(), ioExamples.get(0).first, ba));
//		System.out.println(SFAOperations.getStateInFA(sourceFinite, sourceFinite.getInitialState(), examplesFinite.get(0).first, ba));
		
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		
		// Make target FA total
		SFA<CharPred, Character> targetTotal = SFAOperations.mkTotalFinite(targetFinite, alphabetSet, ba);
		
		// template
//		template = SFAOperations.pseudoNormalize(sourceFinite, ba);
//		System.out.println(template.toDotString(ba));
//		System.out.println(template.getFinalStates());
		
		SFT<CharPred, CharFunc, Character> mySFT = null;
		SFT<CharPred, CharFunc, Character> mySFT2 = null;
		if (template != null) { 	// using a default template right now, fix later
			ConstraintsBV c = new ConstraintsBV(ctx, sourceFinite, targetTotal, alphabetMap, ba);
			mySFT = c.mkConstraints(sourceFinite.stateCount(), outputBound, fraction, examplesFinite, sourceFinite, null, null, debug).first;
			System.out.println(mySFT.toDotString(ba));
		} else {
			ConstraintsBV c = new ConstraintsBV(ctx, sourceFinite, targetTotal, alphabetMap, ba);
			mySFT = c.mkConstraints(numStates, outputBound, fraction, examplesFinite, null, null, null, debug).first;
			System.out.println(mySFT.toDotString(ba));
			
			// Get second solution if there is one
			mySFT2 = c.mkConstraints(numStates, outputBound, fraction, examplesFinite, null, mySFT, null, debug).first;
			System.out.println(mySFT2.toDotString(ba));
		}
		
		// Call minterm expansion
		SFT<CharPred, CharFunc, Character> mySFTexpanded = SFTOperations.mintermExpansion(mySFT, triple.third, ba);
		System.out.println(mySFTexpanded.toDotString(ba));
		
		for (Pair<String, String> example : ioExamples) {
        	String exampleOutput = SFTOperations.getOutputString(mySFTexpanded, example.first, ba);
        	System.out.println(exampleOutput);
        	assertTrue(exampleOutput.equals(example.second));
        }
		
		System.out.println("Done");
		return mySFTexpanded;
	}
	
	public static SFT<CharPred, CharFunc, Character> customLookaheadConstraintsTest(SFA<CharPred, Character> source, 
			SFA<CharPred, Character> target, int numStates, int numLookaheadStates,
			int outputBound, int[] fraction, List<Pair<String, String>> ioExamples, 
			SFA<CharPred, Character> template, String smtFile, boolean debug) throws TimeoutException {
		HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
		
		// Make finite automata out of source and target
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(source, target, ba);
		
		System.out.println(source.toDotString(ba));
		System.out.println(target.toDotString(ba));
		SFA<CharPred, Character> sourceFinite = triple.first;
		SFA<CharPred, Character> targetFinite = triple.second;
		System.out.println(sourceFinite.toDotString(ba));
		System.out.println(targetFinite.toDotString(ba));
		
		Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterm = triple.third;
		
		List<Pair<String, String>> examplesFinite = finitizeExamples(ioExamples, idToMinterm);
		for (Pair<String, String> example : examplesFinite) {
			System.out.println(example);
		}
		
		Set<Character> sourceAlphabetSet = SFAOperations.alphabetSet(sourceFinite, ba);
		Set<Character> targetAlphabetSet = SFAOperations.alphabetSet(targetFinite, ba);
		Set<Character> alphabetSet = new HashSet<Character>();
		alphabetSet.addAll(sourceAlphabetSet);
		alphabetSet.addAll(targetAlphabetSet);
		
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		
		// Make target FA total
		SFA<CharPred, Character> targetTotal = SFAOperations.mkTotalFinite(targetFinite, alphabetSet, ba);
		
		FSTLookahead<Character, Character> mySFT = null;
		ConstraintsSolverLookahead c = new ConstraintsSolverLookahead(ctx, sourceFinite, targetTotal, alphabetMap, 
				numStates, numLookaheadStates, outputBound, examplesFinite, fraction, template, null, idToMinterm, ba);
		mySFT = c.mkConstraints(smtFile, debug).first;
		FST<Pair<Character, Integer>, Character> lookaheadFT = mySFT.getTransducer();
		FSA<Character> lookaheadAut = mySFT.getAutomaton();
		
		// Get second solution if there is one
//		c = new ConstraintsSolverLookahead(ctx, sourceFinite, targetTotal, alphabetMap, 
//				numStates, numLookaheadStates, outputBound, examplesFinite, fraction, template, mySFT, idToMinterm, ba);
//		FSTLookahead<Character, Character> mySFT2 = c.mkConstraints(smtFile, debug).first;
		
		System.out.println(mySFT.getTransducer().toDotString());
		System.out.println(mySFT.getAutomaton().toDotString());
		
		// Make non-det FT
		FST<Character, Character> nonDetFT = c.mkNonDetFT(lookaheadFT, lookaheadAut);
		System.out.println(nonDetFT.toDotString());
		
		// Call minterm expansion
		SFT<CharPred, CharFunc, Character> mySFTexpanded = FSTOperations.mintermExpansion(nonDetFT, triple.third, ba);
		System.out.println(mySFTexpanded.toDotString(ba));
		
		SFT<CharPred, CharFunc, Character> mySFTrestricted = SFTOperations.mkAllStatesFinal(mySFTexpanded, ba);
		
		for (Pair<String, String> example : ioExamples) {
        	List<String> exampleOutputs = SFTOperations.getAllOutputs(mySFTrestricted, example.first, ba);
        	System.out.println(exampleOutputs);
        	// assertTrue(exampleOutput.equals(example.second));
        }
		
		System.out.println("Done");
		return mySFTexpanded;
	}
	
	static void scriptTest() throws TimeoutException {
        int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("a<scr>a", "aa"));
        examples.add(new Pair<String, String>("a<sct>a", "a<sct>a"));
        
        customConstraintsTest(mySFA01, mySFA02, 3, 4, fraction, examples, null, false);
	}
	
	static void escapeQuotesTest() throws TimeoutException {
		SFA<CharPred, Character> outputSFT16 = mySFT16.getOverapproxOutputSFA(ba);
		SFA<CharPred, Character> output = outputSFT16.determinize(ba);
		SFA<CharPred, Character> target = mySFT17.getOverapproxOutputSFA(ba);
		target = target.determinize(ba);
		
		int[] fraction = new int[] {1, 1};
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("\\\\a", "\\a"));
        examples.add(new Pair<String, String>("\\\\\\\\", "\\\\"));
        examples.add(new Pair<String, String>("abc", "abc"));
        examples.add(new Pair<String, String>("\\\'", "\\\'"));
        
        customConstraintsTest(output, target, 4, 1, fraction, examples, null, false);
	}
	
	static void dosToUnixTest() throws TimeoutException {
		int[] fraction = new int[] {1, 1};
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("abc", "abc"));
        examples.add(new Pair<String, String>("\\r\\n", "\\n"));
        
        customConstraintsTest(mySFA07, mySFA08, mySFA07.stateCount(), 1, fraction, examples, null, false);
	}
	
	
	
	// -------------------------
	// Auxiliary methods
	// -------------------------
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
        
        scriptTest();
        // escapeQuotesTest();
        // dosToUnixTest();
	}

}
