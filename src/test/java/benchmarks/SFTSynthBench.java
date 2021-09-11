package benchmarks;

import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.Test;
import org.sat4j.specs.TimeoutException;

import SFT.MalwareFingerprintingDecode;
import automata.sfa.SFA;
import solver.ConstraintsTestSymbolic;
import solver.Driver;
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
import utilities.Triple;

public class SFTSynthBench {
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
	
	
	public void escapeQuotesSynthesis() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> EscapeQuotesBuggy = SFTBench.mkEscapeQuotesBuggy();
		System.out.println(EscapeQuotesBuggy.toDotString(ba));
		
		SFT<CharPred, CharFunc, Character> EscapeQuotes = SFTBench.mkEscapeQuotes();
		System.out.println(EscapeQuotes.toDotString(ba));
		
		SFA<CharPred, Character> inputLang = EscapeQuotesBuggy.getDomain(ba);
		System.out.println(inputLang.toDotString(ba));
		
		SFA<CharPred, Character> outputLang = EscapeQuotesBuggy.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		System.out.println(outputLang.toDotString(ba));
		
		SFA<CharPred, Character> outputCorrect = EscapeQuotes.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		System.out.println(outputCorrect.toDotString(ba));
		
		SFA<CharPred, Character> source = inputLang;
		SFA<CharPred, Character> target = outputCorrect;
		
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("ab\"ab", "ab\\\"ab"));
		examples.add(new Pair<String, String>("ab\\\\ab", "ab\\\\ab"));
		examples.add(new Pair<String, String>("ab\\\"ab", "ab\\\"ab"));
		examples.add(new Pair<String, String>("ab\\ab", "ab\\ab"));
		examples.add(new Pair<String, String>("\\", "\\"));
		
		Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String> result = 
				Driver.runAlgorithm(source, target, 2, 2, fraction, examples, null, null, null, "src/test/java/benchmarks/Outputs/escapeQuotes_out", "escapeQuotesSynth");
	}
	
	private static SFT<CharPred, CharFunc, Character> mkFiniteEscapeQuotesBuggy() throws TimeoutException {
		List<SFTMove<CharPred, CharFunc, Character>> transitions16 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		CharPred quotes = new CharPred('\"');
		CharPred backslash = new CharPred('\\');
		CharPred aChar = new CharPred('a');
		List<CharFunc> output161 = new ArrayList<CharFunc>();
		output161.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, aChar, output161));
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
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, quotes, output165));
		List<CharFunc> output166 = new ArrayList<CharFunc>();
		output166.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, aChar, output166));
		Map<Integer, Set<List<Character>>> finStatesAndTails16 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails16.put(0, new HashSet<List<Character>>());
		finStatesAndTails16.put(1, new HashSet<List<Character>>());
		return SFT.MkSFT(transitions16, 0, finStatesAndTails16, ba);
	}
	
	private static SFT<CharPred, CharFunc, Character> mkFiniteEscapeQuotes() throws TimeoutException {
		List<SFTMove<CharPred, CharFunc, Character>> transitions16 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		CharPred quotes = new CharPred('\"');
		CharPred backslash = new CharPred('\\');
		CharPred aChar = new CharPred('a');
		List<CharFunc> output161 = new ArrayList<CharFunc>();
		output161.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, aChar, output161));
		List<CharFunc> output162 = new ArrayList<CharFunc>();
		output162.add(new CharConstant('\\'));
		output162.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, quotes, output162));
		List<CharFunc> output163 = new ArrayList<CharFunc>();
		output163.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, backslash, output163));
		List<CharFunc> output164 = new ArrayList<CharFunc>();
		output164.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, backslash, output164));
		List<CharFunc> output165 = new ArrayList<CharFunc>();
		output165.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, quotes, output165));
		List<CharFunc> output166 = new ArrayList<CharFunc>();
		output166.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, aChar, output166));
		Map<Integer, Set<List<Character>>> finStatesAndTails16 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails16.put(0, new HashSet<List<Character>>());
		finStatesAndTails16.put(1, new HashSet<List<Character>>());
		return SFT.MkSFT(transitions16, 0, finStatesAndTails16, ba);
	}

	@Test
	public void finiteEscapeQuotesBuggyRepair() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> EscapeQuotesBuggy = mkFiniteEscapeQuotesBuggy();
		System.out.println(EscapeQuotesBuggy.toDotString(ba));
		
		SFT<CharPred, CharFunc, Character> EscapeQuotes = mkFiniteEscapeQuotes();
		System.out.println(EscapeQuotes.toDotString(ba));
		
		SFA<CharPred, Character> outputLang = EscapeQuotesBuggy.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		System.out.println(outputLang.toDotString(ba));
		
		SFA<CharPred, Character> outputCorrect = EscapeQuotes.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		System.out.println(outputCorrect.toDotString(ba));
		
		SFA<CharPred, Character> source = outputLang;
		SFA<CharPred, Character> target = outputCorrect;
		System.out.println(source.includedIn(target, ba));
		
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("a\\\"a", "a\\\"a"));
		examples.add(new Pair<String, String>("a\\\\a", "a\\a"));
		examples.add(new Pair<String, String>("a\\\\\"a", "a\\\"a"));
		examples.add(new Pair<String, String>("a\\\\\\\\a", "a\\\\a"));
		// examples.add(new Pair<String, String>("a\\", "a\\"));
		
		Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String> result = 
				Driver.runAlgorithm(source, target, 4, 1, fraction, examples, source, null, null, "src/test/java/benchmarks/Outputs/escapeQuotesFinite_out", null);
		
		SFT<CharPred, CharFunc, Character> repairSFT = EscapeQuotesBuggy.composeWith(result.first.first, ba);
		System.out.println(repairSFT.toDotString(ba));
	}
	
	
	public void finiteEscapeQuotesSynthesis() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> EscapeQuotesBuggy = mkFiniteEscapeQuotesBuggy();
		System.out.println(EscapeQuotesBuggy.toDotString(ba));
		
		SFT<CharPred, CharFunc, Character> EscapeQuotes = mkFiniteEscapeQuotes();
		System.out.println(EscapeQuotes.toDotString(ba));
		
		SFA<CharPred, Character> inputLang = EscapeQuotesBuggy.getDomain(ba);
		System.out.println(inputLang.toDotString(ba));
		
		SFA<CharPred, Character> outputLang = EscapeQuotesBuggy.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		System.out.println(outputLang.toDotString(ba));
		
		SFA<CharPred, Character> outputCorrect = EscapeQuotes.getOverapproxOutputSFA(ba).removeEpsilonMoves(ba).determinize(ba);
		System.out.println(outputCorrect.toDotString(ba));
		
		SFA<CharPred, Character> source = inputLang;
		SFA<CharPred, Character> target = outputCorrect;
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("a\"a", "a\\\"a"));
		examples.add(new Pair<String, String>("a\\\\a", "a\\\\a"));
		examples.add(new Pair<String, String>("a\\\"a", "a\\\"a"));
		examples.add(new Pair<String, String>("a\\a", "a\\a"));
		examples.add(new Pair<String, String>("\\", "\\"));
		
		Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String> result = 
				Driver.runAlgorithm(source, target, 2, 2, fraction, examples, null, null, null, "src/test/java/benchmarks/Outputs/escapeQuotesFinite_out", "escapeQuotesSynth");
	}
	
	
	public void escapeBracketsSynthesis() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> EscapeBrackets = SFTBench.mkEscapeBrackets();
		System.out.println(EscapeBrackets.toDotString(ba));
		
		SFA<CharPred, Character> inputLang = EscapeBrackets.getDomain(ba);
		System.out.println(inputLang.toDotString(ba));
		
		SFA<CharPred, Character> outputLang = EscapeBrackets.getOverapproxOutputSFA(ba).determinize(ba);
		System.out.println(EscapeBrackets.getOverapproxOutputSFA(ba).toDotString(ba));
		System.out.println(outputLang.toDotString(ba));
		
		SFA<CharPred, Character> source = inputLang;
		SFA<CharPred, Character> target = outputLang;
		
		
		int[] fraction = new int[] {4, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("<", "&lt;"));
		examples.add(new Pair<String, String>(">", "&gt;"));
		
//		Triple<Pair<SFT<CharPred, CharFunc, Character>, Long>, Pair<SFT<CharPred, CharFunc, Character>, Long>, String> result = 
//				Driver.runAlgorithm(source, target, 1, 4, fraction, examples, null, "src/test/java/benchmarks/Benchmarks/escapeBrackets_out", "escapeBracketsSynth");
	
		ConstraintsTestSymbolic.customConstraintsTest(source, target, 1, 4, fraction, examples, null, false);
	}
	
	private static List<Character> lOfS(String s) {
		List<Character> l = new ArrayList<Character>();
		char[] ca = s.toCharArray();
		for (int i = 0; i < s.length(); i++)
			l.add(ca[i]);
		return l;
	}
}
