package z3;

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
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;
import solver.Constraints;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import theory.characters.StdCharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import utilities.Pair;
import utilities.SFAprovider;
import utilities.Triple;

public class ConstraintsTestSymbolic {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	private static SFA<CharPred, Character> mySFA01;
	private static SFA<CharPred, Character> mySFA02;
	
	public static void mkSFAs() throws TimeoutException {
		String regex = "abc|de";
		SFAprovider test = new SFAprovider(regex, ba);
		SFA<CharPred, Character> sfa = test.getSFA();
		
		/* mySFA01 */
		String regex1 = "\\w<\\w*>\\w";
		SFAprovider test1 = new SFAprovider(regex1, ba);
		mySFA01 = (test1.getSFA()).removeEpsilonMoves(ba);
		System.out.println(mySFA01.toDotString(ba));
		
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
		System.out.println(mySFA02.toDotString(ba));
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
	static SFT<CharPred, CharFunc, Character> customConstraintsTest(Context ctx, SFA<CharPred, Character> source, 
			SFA<CharPred, Character> target, int numStates, int outputBound, int[] fraction, 
			List<Pair<String, String>> ioExamples, SFA<CharPred, Character> template, boolean debug) throws TimeoutException {
		
		// Make finite automata out of source and target
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(source, target, ba);
		
		SFA<CharPred, Character> sourceFinite = triple.first;
		SFA<CharPred, Character> targetFinite = triple.second;
		System.out.println(sourceFinite.toDotString(ba));
		System.out.println(targetFinite.toDotString(ba));
		
		Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterm = triple.third;
		System.out.println(idToMinterm);
		
		List<Pair<String, String>> examplesFinite = finitizeExamples(ioExamples, idToMinterm);
		System.out.println(SFAOperations.finitizeStringMinterms(ioExamples.get(0).first, idToMinterm, ba));
		System.out.println(SFAOperations.finitizeStringMinterms(ioExamples.get(0).second, idToMinterm, ba));
		System.out.println(SFAOperations.finitizeStringMinterms(ioExamples.get(1).first, idToMinterm, ba));
		System.out.println(SFAOperations.finitizeStringMinterms(ioExamples.get(1).second, idToMinterm, ba));
		
		
		Set<Character> sourceAlphabetSet = SFAOperations.alphabetSet(sourceFinite, ba);
		Set<Character> targetAlphabetSet = SFAOperations.alphabetSet(targetFinite, ba);
		Set<Character> alphabetSet = new HashSet<Character>();
		alphabetSet.addAll(sourceAlphabetSet);
		alphabetSet.addAll(targetAlphabetSet);
		
		HashMap<Character, Integer> alphabetMap = SFAOperations.mkAlphabetMap(alphabetSet);
		
		// Make target FA total
		SFA<CharPred, Character> targetTotal = SFAOperations.mkTotalFinite(targetFinite, alphabetSet, ba);
		
		Constraints c = new Constraints(ctx, sourceFinite, targetTotal, alphabetMap, ba);
		SFT<CharPred, CharFunc, Character> mySFT = c.mkConstraints(numStates, outputBound, fraction, examplesFinite, template, debug);
		System.out.println(mySFT.toDotString(ba));
		
		// Call minterm expansion
		SFT<CharPred, CharFunc, Character> mySFTexpanded = SFTOperations.mintermExpansion(mySFT, triple.third, ba);
		
		for (Pair<String, String> example : ioExamples) {
			// Call outputOn
        	List<Character> exampleOutput = mySFTexpanded.outputOn(lOfS(example.first), ba);
            assertTrue(exampleOutput.equals(lOfS(example.second)));
        }
		
		return null;
	}
	
	static void scriptTest() throws TimeoutException {
		HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        
        int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("a<scr>a", "aa"));
        examples.add(new Pair<String, String>("a<sct>a", "a<sct>a"));
        
        customConstraintsTest(ctx, mySFA01, mySFA02, 3, 4, fraction, examples, null, false);
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
	}

}
