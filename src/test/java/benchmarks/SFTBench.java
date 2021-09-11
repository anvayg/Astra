package benchmarks;

import static org.junit.Assert.assertTrue;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import org.junit.Test;
import org.sat4j.specs.TimeoutException;

import SFT.GetTag;
import automata.SFAOperations;
import automata.SFTOperations;
import automata.sfa.SFA;
import solver.ConstraintsTestSymbolic;
import solver.Driver;
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
import utilities.Triple;

public class SFTBench {
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	/* Benchmarks from: https://www.doc.ic.ac.uk/~livshits/papers/pdf/popl12.pdf 
	 * Reference implementations: https://github.com/lorisdanto/symbolicautomata/blob/master/benchmarks/src/main/java/SFT/
	 * */
	
	// TODO: move getTags (cleaned up) here
	
	public static SFT<CharPred, CharFunc, Character> mkEscapeQuotesBuggy() throws TimeoutException {
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
		finStatesAndTails16.put(1, new HashSet<List<Character>>());
		return SFT.MkSFT(transitions16, 0, finStatesAndTails16, ba);
	}
	
	public static SFT<CharPred, CharFunc, Character> mkEscapeQuotes() throws TimeoutException {
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
		finStatesAndTails17.put(1, new HashSet<List<Character>>());
		return SFT.MkSFT(transitions17, 0, finStatesAndTails17, ba);
	}
	
	
	public void escapeQuotesBuggyRepair() throws TimeoutException {
		SFT<CharPred, CharFunc, Character> EscapeQuotesBuggy = mkEscapeQuotesBuggy();
		System.out.println(EscapeQuotesBuggy.toDotString(ba));
		
		SFT<CharPred, CharFunc, Character> EscapeQuotes = mkEscapeQuotes();
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
		examples.add(new Pair<String, String>("ab\\\"ab", "ab\\\"ab"));
		examples.add(new Pair<String, String>("ab\\\\\"ab", "ab\\\"ab"));
		examples.add(new Pair<String, String>("ab\\\\\"ab", "ab\\\"ab"));
		examples.add(new Pair<String, String>("ab\\\\\\\\ab", "ab\\\\ab"));
		
		SFT<CharPred, CharFunc, Character> synthSFT = ConstraintsTestSymbolic.customConstraintsTest(source, target, 7, 1, fraction, examples, source, false);
		System.out.println(synthSFT.toDotString(ba));
				
		SFT<CharPred, CharFunc, Character> repairSFT = EscapeQuotesBuggy.composeWith(synthSFT, ba);
		System.out.println(repairSFT.toDotString(ba));
	}
	
	
	/* Repair */
	
	public static SFT<CharPred, CharFunc, Character> mkCaesarCipher() throws TimeoutException {
		List<SFTMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();

		List<CharFunc> output00 = new ArrayList<CharFunc>();
		output00.add(new CharOffset(3));
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, StdCharPred.ALPHA_NUM, output00));
		

		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails.put(0, new HashSet<List<Character>>());

		return SFT.MkSFT(transitions, 0, finStatesAndTails, ba);
	}
	
	public static SFT<CharPred, CharFunc, Character> mkSwapCase() throws TimeoutException {
		List<SFTMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();

		List<CharFunc> output00 = new ArrayList<CharFunc>();
		output00.add(CharOffset.TO_LOWER_CASE);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, StdCharPred.UPPER_ALPHA, output00));
		
		List<CharFunc> output001 = new ArrayList<CharFunc>();
		output001.add(CharOffset.TO_UPPER_CASE);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, StdCharPred.LOWER_ALPHA, output001));
		
		List<CharFunc> output002 = new ArrayList<CharFunc>();
		output002.add(CharOffset.IDENTITY);
		CharPred notUpperOrLower = ba.MkAnd(ba.MkNot(StdCharPred.UPPER_ALPHA), ba.MkNot(StdCharPred.LOWER_ALPHA));
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, notUpperOrLower, output002));

		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails.put(0, new HashSet<List<Character>>());

		return SFT.MkSFT(transitions, 0, finStatesAndTails, ba);
	}
	
	public static SFT<CharPred, CharFunc, Character> mkEscapeBrackets() throws TimeoutException {
		List<SFTMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();

		List<CharFunc> output00 = new ArrayList<CharFunc>();
		output00.add(new CharConstant('&'));
		output00.add(new CharConstant('l'));
		output00.add(new CharConstant('t'));
		output00.add(new CharConstant(';'));
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('<'), output00));
		
		List<CharFunc> output001 = new ArrayList<CharFunc>();
		output001.add(new CharConstant('&'));
		output001.add(new CharConstant('g'));
		output001.add(new CharConstant('t'));
		output001.add(new CharConstant(';'));
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('>'), output001));
		
		List<CharFunc> output002 = new ArrayList<CharFunc>();
		output002.add(CharOffset.IDENTITY);
		CharPred elseCase = ba.MkAnd(ba.MkNot(new CharPred('<')), ba.MkNot(new CharPred('>')));
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, elseCase, output002));

		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails.put(0, new HashSet<List<Character>>());

		return SFT.MkSFT(transitions, 0, finStatesAndTails, ba);
	}
	
	public static SFT<CharPred, CharFunc, Character> mkAnsi() throws TimeoutException {
		List<SFTMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();

		List<CharFunc> output00 = new ArrayList<CharFunc>();
		output00.add(CharOffset.IDENTITY);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, StdCharPred.TRUE, output00));

		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails.put(0, new HashSet<List<Character>>());

		return SFT.MkSFT(transitions, 0, finStatesAndTails, ba);
	}
	
	static final String AB = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
	
	public static List<SFT<CharPred, CharFunc, Character>> createRepairBenchmarks(SFT<CharPred, CharFunc, Character> aut) throws TimeoutException {
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = new ArrayList<SFT<CharPred, CharFunc, Character>>();
		
		LinkedList<SFTInputMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTInputMove<CharPred, CharFunc, Character>>();

		for (Integer state : aut.getStates()) {
			transitions.addAll(aut.getInputMovesFrom(state));
		}

		Random generator = new Random(1); 	// use same seed to get the same results

		/* Pick a transition to modify */
		int ran = generator.nextInt(transitions.size());

		SFTInputMove<CharPred, CharFunc, Character> toModify = transitions.get(ran);

		/* New outputs */
		List<CharFunc> newOutput = new ArrayList<CharFunc>();
		newOutput.add(new CharConstant(AB.charAt(generator.nextInt(AB.length()))));
		SFTInputMove<CharPred, CharFunc, Character> newTrans = 
				new SFTInputMove<CharPred, CharFunc, Character>(toModify.from, toModify.to, toModify.guard, newOutput);
		
		/* New transitions */
		LinkedList<SFTMove<CharPred, CharFunc, Character>> newTransitions = (LinkedList<SFTMove<CharPred, CharFunc, Character>>) transitions.clone();
		newTransitions.remove(ran);
		newTransitions.add(newTrans);
		
		/* Modified SFT-1 */
		SFT<CharPred, CharFunc, Character> modSFT1 = SFT.MkSFT(newTransitions, aut.getInitialState(), aut.getFinalStatesAndTails(), ba);
		modifiedSFTs.add(modSFT1);
		
		
		
		/* Pick a transition to delete */
		ran = generator.nextInt(transitions.size());
		
		newTransitions = (LinkedList<SFTMove<CharPred, CharFunc, Character>>) transitions.clone();
		newTransitions.remove(ran);
		
		/* Modified SFT-2 */
		SFT<CharPred, CharFunc, Character> modSFT2 = SFT.MkSFT(newTransitions, aut.getInitialState(), aut.getFinalStatesAndTails(), ba);
		modifiedSFTs.add(modSFT2);
		
		
		/* Add a random character to a transition */

		ran = generator.nextInt(transitions.size());
		
		toModify = transitions.get(ran);
		
		/* New outputs */
		newOutput = new ArrayList<CharFunc>();
		newOutput.addAll(toModify.outputFunctions);
		newOutput.add(new CharConstant(AB.charAt(generator.nextInt(AB.length()))));
		newTrans = new SFTInputMove<CharPred, CharFunc, Character>(toModify.from, toModify.to, toModify.guard, newOutput);
		
		/* New transitions */
		newTransitions = (LinkedList<SFTMove<CharPred, CharFunc, Character>>) transitions.clone();
		newTransitions.remove(ran);
		newTransitions.add(newTrans);
		
		/* Modified SFT-3 */
		SFT<CharPred, CharFunc, Character> modSFT3 = SFT.MkSFT(newTransitions, aut.getInitialState(), aut.getFinalStatesAndTails(), ba);
		modifiedSFTs.add(modSFT3);
		
		return modifiedSFTs;
	}
	
	public static Pair<SFT<CharPred, CharFunc, Character>, SFA<CharPred, Character>> computeUnchangedDomain(SFT<CharPred, CharFunc, Character> trans, 
			SFT<CharPred, CharFunc, Character> modTrans) throws TimeoutException {
		LinkedList<SFTInputMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTInputMove<CharPred, CharFunc, Character>>();

		for (Integer state : trans.getStates()) {
			transitions.addAll(trans.getInputMovesFrom(state));
		}
		
		LinkedList<SFTInputMove<CharPred, CharFunc, Character>> modTransitions = new LinkedList<SFTInputMove<CharPred, CharFunc, Character>>();

		for (Integer state : modTrans.getStates()) {
			modTransitions.addAll(modTrans.getInputMovesFrom(state));
		}
		
		LinkedList<SFTMove<CharPred, CharFunc, Character>> unchangedTransitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		
		for (SFTInputMove<CharPred, CharFunc, Character> transition : transitions) {
			if (modTransitions.contains(transition)) {
				unchangedTransitions.add(transition);
			}
		}
		
		SFT<CharPred, CharFunc, Character> unchangedSFT = SFT.MkSFT(unchangedTransitions, trans.getInitialState(), trans.getFinalStatesAndTails(), ba);
		
		return new Pair<SFT<CharPred, CharFunc, Character>, SFA<CharPred, Character>>(unchangedSFT, unchangedSFT.getDomain(ba));
	}
	
	
	public void modMkSwapCase1Repair() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> trans = mkSwapCase();
		System.out.println(trans.toDotString(ba));
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(trans);
		
		SFT<CharPred, CharFunc, Character> modSFT = modifiedSFTs.get(0);
		System.out.println(modSFT.toDotString(ba));
		
		Pair<SFT<CharPred, CharFunc, Character>, SFA<CharPred, Character>> unchanged = computeUnchangedDomain(trans, modSFT);
		SFT<CharPred, CharFunc, Character> correctSFT = unchanged.first;
		SFA<CharPred, Character> correctInputSet = unchanged.second;
		
		SFA<CharPred, Character> inputLang = modSFT.getDomain(ba);
		SFA<CharPred, Character> source = inputLang.minus(correctInputSet, ba).determinize(ba);
		SFA<CharPred, Character> target = trans.getOverapproxOutputSFA(ba);
		
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = SFTOperations.getMinterms(modSFT, ba);
		
		int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("A23B", "a23b"));
        examples.add(new Pair<String, String>("[h\\Q", "[H\\q"));
        
        
        RunBenchmarks.runRepairBenchmark(correctSFT, source, target, minterms, 1, 1, fraction, examples, null, "modSwapCase1", null);
        
        RunBenchmarks.runRepairBenchmark(correctSFT, source, target, minterms, 1, 1, fraction, examples, null, "modSwapCase1", "testOutputFile");
	}
	
	
	public void modMkSwapCase2() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> trans = mkSwapCase();
		System.out.println(trans.toDotString(ba));
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(trans);
		
		SFT<CharPred, CharFunc, Character> modSFT = modifiedSFTs.get(1);
		System.out.println(modSFT.toDotString(ba));
		
		Pair<SFT<CharPred, CharFunc, Character>, SFA<CharPred, Character>> unchanged = computeUnchangedDomain(trans, modSFT);
		SFT<CharPred, CharFunc, Character> correctSFT = unchanged.first;
		SFA<CharPred, Character> correctInputSet = unchanged.second;
		
		SFA<CharPred, Character> inputLang = trans.getDomain(ba);
		SFA<CharPred, Character> source = inputLang.minus(correctInputSet, ba).determinize(ba);
		SFA<CharPred, Character> target = trans.getOverapproxOutputSFA(ba);
		
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = SFTOperations.getMinterms(trans, ba); 
			// need to use the orginal transducer's minterms here
		
		int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("a23b", "A23B"));
        examples.add(new Pair<String, String>("&Yl", "&yL"));
        
        RunBenchmarks.runRepairBenchmark(correctSFT, source, target, minterms, 1, 1, fraction, examples, null, "modSwapCase2", null);
	}
	
	
	public void modMkSwapCase3() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> trans = mkSwapCase();
		System.out.println(trans.toDotString(ba));
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(trans);
		
		SFT<CharPred, CharFunc, Character> modSFT = modifiedSFTs.get(2);
		System.out.println(modSFT.toDotString(ba));
		
		Pair<SFT<CharPred, CharFunc, Character>, SFA<CharPred, Character>> unchanged = computeUnchangedDomain(trans, modSFT);
		SFT<CharPred, CharFunc, Character> correctSFT = unchanged.first;
		SFA<CharPred, Character> correctInputSet = unchanged.second;
		
		SFA<CharPred, Character> inputLang = modSFT.getDomain(ba);
		SFA<CharPred, Character> source = inputLang.minus(correctInputSet, ba).determinize(ba);
		SFA<CharPred, Character> target = trans.getOverapproxOutputSFA(ba);
		
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = SFTOperations.getMinterms(modSFT, ba);
		
		int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("A23B", "a23b"));
        examples.add(new Pair<String, String>("[h\\Q", "[H\\q"));
        
        RunBenchmarks.runRepairBenchmark(correctSFT, source, target, minterms, 1, 1, fraction, examples, null, "modSwapCase3", null);
	}
	
	@Test
	public void modEscapeBrackets1() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> trans = mkEscapeBrackets();
		System.out.println(trans.toDotString(ba));
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(trans);
		
		SFT<CharPred, CharFunc, Character> modSFT = modifiedSFTs.get(0);
		System.out.println(modSFT.toDotString(ba));
		
		Pair<SFT<CharPred, CharFunc, Character>, SFA<CharPred, Character>> unchanged = computeUnchangedDomain(trans, modSFT);
		SFT<CharPred, CharFunc, Character> correctSFT = unchanged.first;
		SFA<CharPred, Character> correctInputSet = unchanged.second;
		
		SFA<CharPred, Character> inputLang = modSFT.getDomain(ba);
		SFA<CharPred, Character> source = inputLang.minus(correctInputSet, ba).determinize(ba);
		SFA<CharPred, Character> target = trans.getOverapproxOutputSFA(ba);
		System.out.println(source.toDotString(ba));
		System.out.println(target.toDotString(ba));
		
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = SFTOperations.getMinterms(modSFT, ba);
		// TODO Adding required predicates/minterms
		
		int[] fraction = new int[] {3, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("<", "&lt;"));
        
        RunBenchmarks.runRepairBenchmark(correctSFT, source, target, minterms, 1, 4, fraction, examples, null, "modEscapeBrackets1", null);
	}
	
	
	public void modEscapeBrackets3() throws TimeoutException {
		SFT<CharPred, CharFunc, Character> trans = mkEscapeBrackets();
		System.out.println(trans.toDotString(ba));
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(trans);
		
		SFT<CharPred, CharFunc, Character> modSFT = modifiedSFTs.get(2);
		System.out.println(modSFT.toDotString(ba));
		
		SFA<CharPred, Character> source = modSFT.getDomain(ba);
		SFA<CharPred, Character> target = modSFT.getOverapproxOutputSFA(ba);
		
		
		System.out.println(source.toDotString(ba));
		System.out.println(target.toDotString(ba));
		
	}
	
	
	public void modCaesarCipher1() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> trans = mkCaesarCipher();
		System.out.println(trans.toDotString(ba));
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(trans);
		
		SFT<CharPred, CharFunc, Character> modSFT = modifiedSFTs.get(0);
		System.out.println(modSFT.toDotString(ba));
		
		Pair<SFT<CharPred, CharFunc, Character>, SFA<CharPred, Character>> unchanged = computeUnchangedDomain(trans, modSFT);
		SFT<CharPred, CharFunc, Character> correctSFT = unchanged.first;
		System.out.println(correctSFT.toDotString(ba));
		SFA<CharPred, Character> correctInputSet = unchanged.second;
		
		SFA<CharPred, Character> inputLang = modSFT.getDomain(ba);
		SFA<CharPred, Character> source = inputLang.minus(correctInputSet, ba).determinize(ba);
		SFA<CharPred, Character> target = trans.getOverapproxOutputSFA(ba);
		
		
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = SFTOperations.getMinterms(modSFT, ba);
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("3", "6"));
        
        RunBenchmarks.runRepairBenchmark(correctSFT, source, target, null, 1, 1, fraction, examples, null, "modCaesarCipher1", null);
	}
	
	
	// Introducing bugs in FlashFill synthesis benchmarks
	
	
	
	private static List<Character> lOfS(String s) {
		List<Character> l = new ArrayList<Character>();
		char[] ca = s.toCharArray();
		for (int i = 0; i < s.length(); i++)
			l.add(ca[i]);
		return l;
	}
	
	// TODO
	public static void main(String[] args) {
		try {
			List<SFT<CharPred, CharFunc, Character>> SFTList = new ArrayList<SFT<CharPred, CharFunc, Character>>();
			SFTList.add(mkSwapCase());
			for (SFT<CharPred, CharFunc, Character> aut : SFTList) {
				List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(aut);
			}
		} catch (TimeoutException e) {
			e.printStackTrace();
		}
	}
	
}
