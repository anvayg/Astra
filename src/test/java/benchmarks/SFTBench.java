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
import automata.SFTTemplate;
import automata.fst.FSTMove;
import automata.fst.FSTTemplate;
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
import utilities.SFAprovider;
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
	
	@Test
	public void modMkSwapCase1Repair() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> trans = mkSwapCase();
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(trans);
		
		// Incorrect output for [A-Z] transition
		SFT<CharPred, CharFunc, Character> modSFT = modifiedSFTs.get(0);
		
		SFA<CharPred, Character> target = trans.getOverapproxOutputSFA(ba);
		
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = SFTOperations.getMinterms(modSFT);
		
		int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("A23B", "a23b"));
        examples.add(new Pair<String, String>("[h\\", "[H\\"));
        
        // localization
        Collection<SFTInputMove<CharPred, CharFunc, Character>> badTransitions = SFTOperations.localizeFaults(modSFT, examples);
        
        // Without template
        RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, minterms, 1, 1, fraction, examples, null, "modSwapCase1", null);
        
        // Make template
        SFTTemplate sftTemplate = new SFTTemplate(modSFT, badTransitions);
        
        // With template
        RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, minterms, 1, 1, fraction, examples, sftTemplate, "modSwapCase1", "modSwapCase1_template");
	}
	
	@Test
	public void modMkSwapCase2() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> trans = mkSwapCase();
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(trans);
		
		// Missing a transition
		SFT<CharPred, CharFunc, Character> modSFT = modifiedSFTs.get(1);
		
		SFA<CharPred, Character> target = trans.getOverapproxOutputSFA(ba);
		
		Collection<Pair<CharPred, ArrayList<Integer>>> defaultMinterms = SFTOperations.getMinterms(modSFT); 
		
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = SFTOperations.getMinterms(trans); 
			// need to use the orginal transducer's minterms here
		
		int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("a23b", "A23B"));
        examples.add(new Pair<String, String>("[h\\", "[H\\"));
        
        // localization
        Collection<SFTInputMove<CharPred, CharFunc, Character>> badTransitions = SFTOperations.localizeFaults(modSFT, examples);
        
        // Default minterms (fails)
        RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, defaultMinterms, 1, 1, fraction, examples, null, "modSwapCase2", "modSwapCase2_out");
        
        // Custom minterms (fails)
        RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, minterms, 1, 1, fraction, examples, null, "modSwapCase2", "modSwapCase2_out");
	}
	
	@Test
	public void modMkSwapCase3() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> trans = mkSwapCase();
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(trans);
		
		SFT<CharPred, CharFunc, Character> modSFT = modifiedSFTs.get(2);
		
		SFA<CharPred, Character> target = trans.getOverapproxOutputSFA(ba);
		
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = SFTOperations.getMinterms(modSFT);
		
		int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("A23B", "a23b"));
        examples.add(new Pair<String, String>("[h\\", "[H\\"));
        
        // localization
        Collection<SFTInputMove<CharPred, CharFunc, Character>> badTransitions = SFTOperations.localizeFaults(modSFT, examples);
        
        // Without template
        RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, minterms, 1, 1, fraction, examples, null, "modSwapCase3", null);
        
        // Make template
        SFTTemplate sftTemplate = new SFTTemplate(modSFT, badTransitions);
        
        // With template
        RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, minterms, 1, 1, fraction, examples, sftTemplate, "modSwapCase3", "modSwapCase3_template");
	}
	
	@Test
	public void modEscapeBrackets1() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> trans = mkEscapeBrackets();
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(trans);
		
		SFT<CharPred, CharFunc, Character> modSFT = modifiedSFTs.get(0);
		
		SFA<CharPred, Character> target = trans.getOverapproxOutputSFA(ba);
		
		Collection<Pair<CharPred, ArrayList<Integer>>> defaultMinterms = SFTOperations.getMinterms(modSFT);
		
		// Adding required predicates/minterms
		Set<CharPred> preds = new HashSet<CharPred>();
		preds.addAll(SFTOperations.getPreds(modSFT));
		preds.addAll(SFAOperations.getPreds(target));
		preds.add(new CharPred('g'));
		
		ArrayList<CharPred> predsList = new ArrayList<CharPred>();
		predsList.addAll(preds);
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = ba.GetMinterms(predsList);
		
		int[] fraction = new int[] {4, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("<", "&lt;"));
        examples.add(new Pair<String, String>(">", "&gt;"));
        examples.add(new Pair<String, String>(";gf", ""));
        examples.add(new Pair<String, String>("&t&l", ""));
        
        // localization
        Collection<SFTInputMove<CharPred, CharFunc, Character>> badTransitions = SFTOperations.localizeFaults(modSFT, examples);
        
        // Default minterms, no template
        RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, defaultMinterms, 1, 4, fraction, examples, null, "modEscapeBrackets1", "modEscapeBrackets1_default");
        
        // Custom minterms
        RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, minterms, 1, 4, fraction, examples, null, "modEscapeBrackets1", null);
        
        // Make template
        SFTTemplate sftTemplate = new SFTTemplate(modSFT, badTransitions);
        
        // With template
        RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, minterms, 1, 4, fraction, examples, sftTemplate, "modEscapeBrackets1", "modEscapeBrackets1_template");
	}
	
	@Test
	public void modEscapeBrackets3() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> trans = mkEscapeBrackets();
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(trans);
		
		SFT<CharPred, CharFunc, Character> modSFT = modifiedSFTs.get(2);
		
		SFA<CharPred, Character> target = modSFT.getOverapproxOutputSFA(ba);
		
		Collection<Pair<CharPred, ArrayList<Integer>>> defaultMinterms = SFTOperations.getMinterms(modSFT);
		
		// Adding required predicates/minterms
		Set<CharPred> preds = new HashSet<CharPred>();
		preds.addAll(SFTOperations.getPreds(modSFT));
		preds.addAll(SFAOperations.getPreds(target));
		preds.add(new CharPred('g'));

		ArrayList<CharPred> predsList = new ArrayList<CharPred>();
		predsList.addAll(preds);
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = ba.GetMinterms(predsList);

		int[] fraction = new int[] {4, 1};

		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("<", "&lt;"));
		examples.add(new Pair<String, String>(">", "&gt;"));
		examples.add(new Pair<String, String>(";gf", ""));
		examples.add(new Pair<String, String>("&t&l", ""));
		examples.add(new Pair<String, String>("k", ""));

		// localization
		Collection<SFTInputMove<CharPred, CharFunc, Character>> badTransitions = SFTOperations.localizeFaults(modSFT, examples);

		// Default minterms, no template
		RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, defaultMinterms, 1, 4, fraction, examples, null, "modEscapeBrackets3", "modEscapeBrackets3_default");

		// Custom minterms
		RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, minterms, 1, 4, fraction, examples, null, "modEscapeBrackets3", null);

		// Make template
		SFTTemplate sftTemplate = new SFTTemplate(modSFT, badTransitions);

		// With template
		RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, minterms, 1, 4, fraction, examples, sftTemplate, "modEscapeBrackets3", "modEscapeBrackets3_template");
	}
	
	@Test
	public void modCaesarCipher1() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> trans = mkCaesarCipher();
		List<SFT<CharPred, CharFunc, Character>> modifiedSFTs = createRepairBenchmarks(trans);
		
		SFT<CharPred, CharFunc, Character> modSFT = modifiedSFTs.get(0);
		
		SFA<CharPred, Character> target = trans.getOverapproxOutputSFA(ba);
		
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = SFTOperations.getMinterms(modSFT);
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("3", "6"));
        
        // localization
     	Collection<SFTInputMove<CharPred, CharFunc, Character>> badTransitions = SFTOperations.localizeFaults(modSFT, examples);

     	// Default (fails)
     	RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, minterms, 1, 1, fraction, examples, null, "modCaesarCipher", null);
	}
	
	
	
	
	/* 
	 * Flash-Fill Benchmarks
	 * */
	
	
	// Trying to introduce bugs in FlashFill synthesis benchmarks (synthesizing using only example constraints)
	public void extrAcronym2() throws TimeoutException, IOException {
		String CONFERENCE_NAME_REGEX = "[A-Za-z]+( [A-Za-z]+)*";
		SFA<CharPred, Character> CONFERENCE_NAME = (new SFAprovider(CONFERENCE_NAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba); 
		assertTrue(CONFERENCE_NAME.accepts(lOfS("Principles of Programming Languages"), ba));
		
		String CONFERENCE_ACRONYM_REGEX = "[A-Z][A-Z]*";
		SFA<CharPred, Character> CONFERENCE_ACRONYM = (new SFAprovider(CONFERENCE_ACRONYM_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(CONFERENCE_ACRONYM.accepts(lOfS("POPL"), ba));
		
		int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("Principles of Programming Languages", "POPL"));
        examples.add(new Pair<String, String>("Programming Language Design Implementation", "PLDI"));
        examples.add(new Pair<String, String>("vLU", "V"));
        
        ArrayList<Boolean> config = new ArrayList<Boolean>();
        config.add(true);
        config.add(false);
        config.add(false);
        
        Triple<Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, String> result = 
				Driver.runAlgorithm(CONFERENCE_NAME, CONFERENCE_ACRONYM, 2, 1, fraction, examples, null, null, null, config, "src/test/java/benchmarks/tmpOutput", "extrAcronym");
	}
	
	/* Buggy extrAcronym2 obtained by only using example constraints */
	public static SFT<CharPred, CharFunc, Character> mkBuggyExtrAcronym() throws TimeoutException {
		List<SFTMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();

		List<CharFunc> output000 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, StdCharPred.LOWER_ALPHA, output000));
		
		List<CharFunc> output001 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, StdCharPred.UPPER_ALPHA, output001));
		
		List<CharFunc> output002 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, new CharPred(' '), output002));
		
		List<CharFunc> output100 = new ArrayList<CharFunc>();
		output100.add(new CharOffset(-32));
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, StdCharPred.LOWER_ALPHA, output100));
		
		List<CharFunc> output101 = new ArrayList<CharFunc>();
		output101.add(CharOffset.IDENTITY);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, StdCharPred.UPPER_ALPHA, output101));
		
		List<CharFunc> output102 = new ArrayList<CharFunc>();
		output102.add(CharOffset.IDENTITY);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, new CharPred(' '), output102));

		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails.put(0, new HashSet<List<Character>>());
		finStatesAndTails.put(1, new HashSet<List<Character>>());
		
		return SFT.MkSFT(transitions, 0, finStatesAndTails, ba);
	}
	
	// Benchmark: Repairs buggy ExtrAcronym2
	@Test
	public void repairExtrAcronym() throws TimeoutException, IOException {
		SFT<CharPred, CharFunc, Character> modSFT = mkBuggyExtrAcronym();
		String CONFERENCE_NAME_REGEX = "[A-Za-z]+( [A-Za-z]+)*";
		SFA<CharPred, Character> CONFERENCE_NAME = (new SFAprovider(CONFERENCE_NAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		modSFT = modSFT.domainRestriction(CONFERENCE_NAME, ba);
		System.out.println(modSFT.toDotString(ba));
		
		String CONFERENCE_ACRONYM_REGEX = "[A-Z][A-Z]*";
		SFA<CharPred, Character> target = (new SFAprovider(CONFERENCE_ACRONYM_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		
		Collection<Pair<CharPred, ArrayList<Integer>>> minterms = SFTOperations.getMinterms(modSFT);
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("Principles of Programming Languages", "POPL"));
        examples.add(new Pair<String, String>("Programming Language Design Implementation", "PLDI"));
        examples.add(new Pair<String, String>("vLU", "V"));
        
        // localization
     	Collection<SFTInputMove<CharPred, CharFunc, Character>> badTransitions = SFTOperations.localizeFaults(modSFT, examples);
     	System.out.println(badTransitions);

     	// Default (fails)
     	RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, minterms, 2, 1, fraction, examples, null, "modExtrAcronym2", null);
     	
     	// Make template
     	SFTTemplate sftTemplate = new SFTTemplate(modSFT, badTransitions);

     	// With template (TODO: install timeout)
     	// RunBenchmarks.runRepairBenchmark(modSFT, badTransitions, null, target, minterms, modSFT.stateCount(), 1, fraction, examples, sftTemplate, "modExtrAcronym2", "modExtrAcronym2_template");
	}
	
	
	public void capProb() throws TimeoutException, IOException {
		String UPPERCASENAME_REGEX = "[A-Z][A-Z]*";
		SFA<CharPred, Character> UPPERCASENAME = (new SFAprovider(UPPERCASENAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(UPPERCASENAME.accepts(lOfS("DOE"), ba));
		
		String NAME_REGEX = "[A-Z][a-z]*";
		SFA<CharPred, Character> NAME = (new SFAprovider(NAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(NAME.accepts(lOfS("Doe"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
	    // examples.add(new Pair<String, String>("DOE", "Doe"));
	    // examples.add(new Pair<String, String>("ODE", "Ode"));
	    	// removing example(s)
	    
	    ArrayList<Boolean> config = new ArrayList<Boolean>();
        config.add(true);
        config.add(true);
        config.add(true);
	    
	    Triple<Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, String> result = 
				Driver.runAlgorithm(UPPERCASENAME, NAME, 2, 1, fraction, examples, null, null, null, config, "src/test/java/benchmarks/tmpOutput", "capProb");
	}
	
	
	public void extrQuant() throws TimeoutException, IOException {
		String THINGANDAMOUNT_REGEX = "[a-zA-Z\\s]*[0-9][a-zA-Z\\s0-9]*";
		SFA<CharPred, Character> THINGANDAMOUNT = (new SFAprovider(THINGANDAMOUNT_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(THINGANDAMOUNT.accepts(lOfS("hey look we sure have a lot of corn we have 35 OZ"), ba));
		
		String AMOUNT_EXTRACTED_REGEX = "[0-9][a-zA-Z\\s0-9]*";
		SFA<CharPred, Character> AMOUNT_EXTRACTED = (new SFAprovider(AMOUNT_EXTRACTED_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(AMOUNT_EXTRACTED.accepts(lOfS("35 OZ"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
	    // examples.add(new Pair<String, String>("hey look we sure have a lot of corn we have 35 OZ", "35 OZ"));
        
        ArrayList<Boolean> config = new ArrayList<Boolean>();
        config.add(true);
        config.add(true);
        config.add(true);
        
        Triple<Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, String> result = 
				Driver.runAlgorithm(THINGANDAMOUNT, AMOUNT_EXTRACTED, 2, 1, fraction, examples, null, null, null, config, "src/test/java/benchmarks/tmpOutput", "extrQuant");
	}
	
	/* Buggy extrQuant obtained when no example provided */
	public static SFT<CharPred, CharFunc, Character> mkBuggyExtrQuant() throws TimeoutException {
		List<SFTMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();

		CharPred alphaOrSpace = ba.MkOr(StdCharPred.SPACES, StdCharPred.ALPHA);
		
		List<CharFunc> output000 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, alphaOrSpace, output000));
		
		List<CharFunc> output001 = new ArrayList<CharFunc>();
		output001.add(CharOffset.IDENTITY);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, StdCharPred.NUM, output001));
		
		List<CharFunc> output100 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, alphaOrSpace, output100));
		
		List<CharFunc> output101 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, StdCharPred.NUM, output101));

		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails.put(0, new HashSet<List<Character>>());
		finStatesAndTails.put(1, new HashSet<List<Character>>());

		return SFT.MkSFT(transitions, 0, finStatesAndTails, ba);
	}
	
	// TODO
	public void repairExtrQuant() throws TimeoutException {
		SFT<CharPred, CharFunc, Character> aut = mkBuggyExtrQuant();
		System.out.println(aut.toDotString(ba));
		
	}
	
	
	public void removeLast() throws TimeoutException, IOException {
		String FIRSTLASTNAME_REGEX = "[A-Z][a-z]* [A-Z][a-z]*";
		SFA<CharPred, Character> FIRSTLASTNAME = (new SFAprovider(FIRSTLASTNAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(FIRSTLASTNAME.accepts(lOfS("John Doe"), ba));
		
		String NAME_REGEX = "[A-Z][a-z]*";
		SFA<CharPred, Character> NAME = (new SFAprovider(NAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(NAME.accepts(lOfS("John"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
	    examples.add(new Pair<String, String>("John Doe", "John"));
	    // examples.add(new Pair<String, String>("Anvay Grover", "Anvay"));
	    
	    ArrayList<Boolean> config = new ArrayList<Boolean>();
        config.add(true);
        config.add(true);
        config.add(true);
        
        Triple<Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, String> result = 
				Driver.runAlgorithm(FIRSTLASTNAME, NAME, 2, 1, fraction, examples, null, null, null, config, "src/test/java/benchmarks/tmpOutput", "removeLast");
	}
	
	
	/* Buggy removeLast obtained by giving 1 fewer example */
	public static SFT<CharPred, CharFunc, Character> mkBuggyRemoveLast() throws TimeoutException {
		List<SFTMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();

		List<CharFunc> output000 = new ArrayList<CharFunc>();
		output000.add(CharOffset.IDENTITY);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, StdCharPred.LOWER_ALPHA, output000));
		
		List<CharFunc> output001 = new ArrayList<CharFunc>();
		output001.add(CharOffset.IDENTITY);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, StdCharPred.UPPER_ALPHA, output001));
		
		List<CharFunc> output002 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred(' '), output002));
		
		List<CharFunc> output100 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 1, StdCharPred.LOWER_ALPHA, output100));
		
		List<CharFunc> output101 = new ArrayList<CharFunc>();
		output101.add(CharOffset.TO_LOWER_CASE);
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, StdCharPred.UPPER_ALPHA, output101));
		
		List<CharFunc> output102 = new ArrayList<CharFunc>();
		transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 1, new CharPred(' '), output102));

		Map<Integer, Set<List<Character>>> finStatesAndTails = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails.put(0, new HashSet<List<Character>>());
		finStatesAndTails.put(1, new HashSet<List<Character>>());

		return SFT.MkSFT(transitions, 0, finStatesAndTails, ba);
	}
	
	// TODO
	public void repairRemoveLast() throws TimeoutException {
		SFT<CharPred, CharFunc, Character> aut = mkBuggyExtrQuant();
		System.out.println(aut.toDotString(ba));

	}
	
	
	public void extrOdds() throws TimeoutException, IOException {
		String UNCLEANED_DATA_REGEX = "([(][)]|[0-9][0-9]*)*(([(][0-9][0-9]*/[0-9][0-9]*[)])([(][)]|[0-9][0-9]*)*)*";
		SFA<CharPred, Character> UNCLEANED_DATA = (new SFAprovider(UNCLEANED_DATA_REGEX, ba)).getSFA().removeEpsilonMoves(ba).determinize(ba);
		assertTrue(UNCLEANED_DATA.accepts(lOfS("13(14/15)()21"), ba));
		assertTrue(UNCLEANED_DATA.accepts(lOfS("13()(14/15)()21"), ba));
		assertTrue(UNCLEANED_DATA.accepts(lOfS("(142/12)()21"), ba));
		System.out.println(SFAOperations.getStateInFA(UNCLEANED_DATA, UNCLEANED_DATA.getInitialState(), "13(14/15)()21", ba));
		
		String CLEANEDODDS_REGEX = "([(][0-9][0-9]*/[0-9][0-9]*[)]#)*";
		SFA<CharPred, Character> CLEANEDODDS = (new SFAprovider(CLEANEDODDS_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(CLEANEDODDS.accepts(lOfS("(14/15)#"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
	    examples.add(new Pair<String, String>("3(1/551)2", "(1/551)#"));
	    // examples.add(new Pair<String, String>("(142/12)()21", "(142/12)#"));
	    // examples.add(new Pair<String, String>("5()(70/8)()21", "(70/8)#"));
	    
	    ArrayList<Boolean> config = new ArrayList<Boolean>();
        config.add(true);
        config.add(true);
        config.add(true);
        
        Triple<Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, String> result = 
				Driver.runAlgorithm(UNCLEANED_DATA, CLEANEDODDS, 3, 2, fraction, examples, null, null, null, config, "src/test/java/benchmarks/tmpOutput", "extrOdds");
	}
	
	
	
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
