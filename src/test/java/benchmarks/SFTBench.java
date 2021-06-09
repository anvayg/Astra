package benchmarks;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.Test;
import org.sat4j.specs.TimeoutException;

import automata.SFAOperations;
import automata.sfa.SFA;
import solver.ConstraintsTestSymbolic;
import theory.characters.CharConstant;
import theory.characters.CharFunc;
import theory.characters.CharOffset;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import transducers.sft.SFTInputMove;
import transducers.sft.SFTMove;
import utilities.Pair;
import utilities.SFAprovider;
import SFT.GetTag;
import SFT.MalwareFingerprintingDecode;

public class SFTBench {
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	/* Benchmarks from: https://www.doc.ic.ac.uk/~livshits/papers/pdf/popl12.pdf 
	 * Reference implementations: https://github.com/lorisdanto/symbolicautomata/blob/master/benchmarks/src/main/java/SFT/
	 * */
	
	/* QuicktimeSplitter */
	public static SFT<CharPred, CharFunc, Character> QuicktimeSplitter;
	
	
	public void quicktimeSplitter() throws TimeoutException {
		QuicktimeSplitter = MalwareFingerprintingDecode.MkQuicktimeSplitter();
		System.out.println(QuicktimeSplitter.toDotString(ba));
		System.out.println(QuicktimeSplitter.getFinalStatesAndTails());
		
		SFA<CharPred, Character> domain = QuicktimeSplitter.getDomain(ba).removeEpsilonMoves(ba);
		assertTrue(domain.accepts(lOfS("00#Quicktime7.6.9"), ba));
		assertTrue(domain.accepts(lOfS("0769#Quicktime7.6.9"), ba));
		
		SFA<CharPred, Character> range = QuicktimeSplitter.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("00#Quicktime7.6.9", "#769"));
		examples.add(new Pair<String, String>("0769#Quicktime7.6.9", "0769#"));
		
		ConstraintsTestSymbolic.customConstraintsTest(domain, range, 1, 1, fraction, examples, null, false);
	}
	
	/* QuicktimeMerger */
	public static SFT<CharPred, CharFunc, Character> QuicktimeMerger;
	
	
	public void quicktimeMerger() throws TimeoutException {
		QuicktimeMerger = MalwareFingerprintingDecode.MkQuicktimeMerger();
		System.out.println(QuicktimeMerger.toDotString(ba));
		SFA<CharPred, Character> domain = QuicktimeMerger.getDomain(ba).removeEpsilonMoves(ba);
		SFA<CharPred, Character> range = QuicktimeMerger.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		
		String SOURCE_REGEX = "([#]?[0-9]+)|([0-9]+[#]?)";
		SFA<CharPred, Character> SOURCE = (new SFAprovider(SOURCE_REGEX, ba)).getSFA().removeEpsilonMoves(ba).determinize(ba);
		assertTrue(SOURCE.accepts(lOfS("#769"), ba));
		assertTrue(SOURCE.accepts(lOfS("769#"), ba));
		
		String TARGET_REGEX = "[0-9]+";
		SFA<CharPred, Character> TARGET = (new SFAprovider(TARGET_REGEX, ba)).getSFA().removeEpsilonMoves(ba).determinize(ba);
		assertTrue(TARGET.accepts(lOfS("769"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("#769", "769"));
		examples.add(new Pair<String, String>("769#", "769"));
		
		ConstraintsTestSymbolic.customConstraintsTest(domain, range, 1, 1, fraction, examples, null, false);
		
		ConstraintsTestSymbolic.customConstraintsTest(SOURCE, TARGET, 1, 1, fraction, examples, null, false);
	}
	
	/* QuicktimePadder: requires memory? or non-determinism? */
	
	
	/* GetTags */
	public static SFT<CharPred, CharFunc, Character> GetTags;
	
	/* GetTags */
	public static SFT<CharPred, CharFunc, Character> GetTagsBuggy;
	
	/* Missing transition from state 2 to state 1 */
	private static SFT<CharPred, CharFunc, Character> MkGetTagsSFTBuggy() throws TimeoutException {
		List<SFTMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();

		List<CharFunc> output00 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, ba.MkNot(new CharPred('<')), output00));

		List<CharFunc> output01 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, new CharPred('<'), output01));

		List<CharFunc> output11 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 1, new CharPred('<'), output11));

		List<CharFunc> output12 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 2, ba.MkNot(new CharPred('<')), output12));

		List<CharFunc> output13 = new ArrayList<CharFunc>();
		output13.add(new CharConstant('<'));
		output13.add(CharOffset.IDENTITY);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 3, ba.MkNot(new CharPred('<')), output13));

		List<CharFunc> output20 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(2, 0, ba.MkAnd(ba.MkNot(new CharPred('<')), ba.MkNot(new CharPred('>'))), output20));

		List<CharFunc> output30 = new ArrayList<CharFunc>();
		output30.add(CharOffset.IDENTITY);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(3, 0, new CharPred('>'), output30));

		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails.put(0, new HashSet<List<Character>>());
		finStatesAndTails.put(1, new HashSet<List<Character>>());
		finStatesAndTails.put(2, new HashSet<List<Character>>());

		return SFT.MkSFT(transitions, 0, finStatesAndTails, ba);
	}
	
	/* Assume that there are no substrings of the form '<a' in the input, for experimenting */
	private static SFT<CharPred, CharFunc, Character> MkGetTagsSFTMod() throws TimeoutException {
		List<SFTMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();

		List<CharFunc> output00 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, ba.MkNot(new CharPred('<')), output00));

		List<CharFunc> output01 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, new CharPred('<'), output01));

		List<CharFunc> output11 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 1, new CharPred('<'), output11));

		List<CharFunc> output13 = new ArrayList<CharFunc>();
		output13.add(new CharConstant('<'));
		output13.add(CharOffset.IDENTITY);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 3, ba.MkNot(new CharPred('<')), output13));

		List<CharFunc> output30 = new ArrayList<CharFunc>();
		output30.add(CharOffset.IDENTITY);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(3, 0, new CharPred('>'), output30));

		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails.put(0, new HashSet<List<Character>>());
		finStatesAndTails.put(1, new HashSet<List<Character>>());

		return SFT.MkSFT(transitions, 0, finStatesAndTails, ba);
	}
	
	
	public void getTags() throws TimeoutException {
		GetTagsBuggy = MkGetTagsSFTBuggy();
		GetTags = GetTag.MkGetTagsSFT();
		System.out.println(GetTagsBuggy.toDotString(ba));
		System.out.println(GetTags.toDotString(ba));
		
		SFA<CharPred, Character> inputLang = GetTagsBuggy.getDomain(ba).removeEpsilonMoves(ba);
		System.out.println(inputLang.toDotString(ba));
		
		SFA<CharPred, Character> inputCorrect = GetTags.getDomain(ba).removeEpsilonMoves(ba);
		System.out.println(inputCorrect.toDotString(ba));
		
		SFA<CharPred, Character> source = inputCorrect.minus(inputLang, ba).determinize(ba);
		assertTrue(source.accepts(lOfS("<<s<"), ba));
		assertTrue(source.accepts(lOfS("<<s<s>"), ba));
		assertTrue(source.accepts(lOfS("<<s<st"), ba));
		System.out.println(source.toDotString(ba));
	
		SFA<CharPred, Character> target = GetTags.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		System.out.println(target.toDotString(ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("<<s<", ""));
		examples.add(new Pair<String, String>("<<s<s>", "<s>"));
		examples.add(new Pair<String, String>("<<s<st", ""));
		SFT<CharPred, CharFunc, Character> synthSFT = ConstraintsTestSymbolic.customConstraintsTest(source, target, 7, 1, fraction, examples, source, false);
		
		// restrict domain to add final states
		SFT<CharPred, CharFunc, Character> restrictSFT = synthSFT.domainRestriction(source, ba);
		
		SFT<CharPred, CharFunc, Character> repairSFT = GetTagsBuggy.unionWith(restrictSFT, ba);
		System.out.println(repairSFT.toDotString(ba));
		System.out.println(repairSFT.getInitialState());
	}
	
	/* Deterministic variant of GetTags */
	
	public void getTagsMod() throws TimeoutException {
		GetTags = MkGetTagsSFTMod();
		System.out.println(GetTags.toDotString(ba));
		System.out.println(GetTags.isDeterministic());
		
		SFA<CharPred, Character> domain = GetTags.getDomain(ba).removeEpsilonMoves(ba).determinize(ba);
		assertTrue(domain.accepts(lOfS(""), ba));
		assertTrue(domain.accepts(lOfS(""), ba));
		
		SFA<CharPred, Character> range = GetTags.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		
		System.out.println(domain);
		System.out.println(range);
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("<<s>", "<s>"));
		examples.add(new Pair<String, String>("<s><t>", "<s><t>"));
		
		ConstraintsTestSymbolic.customConstraintsTest(domain, range, 3, 2, fraction, examples, null, false);
	}
	
	private static SFT<CharPred, CharFunc, Character> mkEscapeQuotesBuggy() throws TimeoutException {
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
		return SFT.MkSFT(transitions16, 0, finStatesAndTails16, ba);
	}
	
	private static SFT<CharPred, CharFunc, Character> mkEscapeQuotes() throws TimeoutException {
		CharPred quotes = ba.MkOr(new CharPred('\''), new CharPred('\"'));
		CharPred backslash = new CharPred('\\');
		CharPred notQuotesAndBackslash = ba.MkAnd(ba.MkNot(quotes), ba.MkNot(backslash));
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
		return SFT.MkSFT(transitions17, 0, finStatesAndTails17, ba);
	}
	
	/* Repair escapeQuotesBuggy */
	@Test
	public void escapeQuotesBuggyRepair() throws TimeoutException {
		SFT<CharPred, CharFunc, Character> EscapeQuotesBuggy = mkEscapeQuotesBuggy();
		System.out.println(EscapeQuotesBuggy.toDotString(ba));
		
		SFT<CharPred, CharFunc, Character> EscapeQuotes = mkEscapeQuotes();
		System.out.println(EscapeQuotes.toDotString(ba));
		
		SFA<CharPred, Character> inputLang = EscapeQuotesBuggy.getDomain(ba).removeEpsilonMoves(ba);
		System.out.println(inputLang.toDotString(ba));
		
		SFA<CharPred, Character> inputCorrect = EscapeQuotes.getDomain(ba).removeEpsilonMoves(ba);
		System.out.println(inputCorrect.toDotString(ba));
		
		SFA<CharPred, Character> outputLang = EscapeQuotesBuggy.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		System.out.println(outputLang.toDotString(ba));
		
		SFA<CharPred, Character> outputCorrect = EscapeQuotes.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		System.out.println(outputCorrect.toDotString(ba));
		
		
		SFA<CharPred, Character> outputDiff = outputLang.minus(outputCorrect, ba);
		System.out.println(outputDiff.toDotString(ba));
		
		
		SFA<CharPred, Character> source = outputDiff;
		SFA<CharPred, Character> target = outputCorrect;
		
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("\\\\\"", "\\\""));
		// examples.add(new Pair<String, String>("\\\\\'", "\\\'"));
		examples.add(new Pair<String, String>("\\\\\"\\\"", "\\\"\\\"")); 	
		examples.add(new Pair<String, String>("\\\\\\\\\\\\\"", "\\\\\\\""));
		examples.add(new Pair<String, String>("\\\\\"\\\\\"", "\\\"\\\""));
		
		SFT<CharPred, CharFunc, Character> synthSFT = ConstraintsTestSymbolic.customConstraintsTest(source, target, 7, 1, fraction, examples, source, false);
		System.out.println(synthSFT.toDotString(ba));
		
		// restrict domain to add final states
		SFT<CharPred, CharFunc, Character> restrictSFT = synthSFT.domainRestriction(source, ba);
		System.out.println(restrictSFT.toDotString(ba));
				
		SFT<CharPred, CharFunc, Character> repairSFT = EscapeQuotesBuggy.composeWith(restrictSFT, ba);
		System.out.println(repairSFT.toDotString(ba));
	}
	
	private static List<Character> lOfS(String s) {
		List<Character> l = new ArrayList<Character>();
		char[] ca = s.toCharArray();
		for (int i = 0; i < s.length(); i++)
			l.add(ca[i]);
		return l;
	}
}
