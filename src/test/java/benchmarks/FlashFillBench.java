package benchmarks;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;
import org.sat4j.specs.TimeoutException;

import automata.SFAOperations;
import automata.sfa.SFA;
import solver.ConstraintsTestSymbolic;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import utilities.Pair;
import utilities.SFAprovider;

public class FlashFillBench {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	/* Benchmarks from: 
	 * https://github.com/amiltner/SymmetricLensSynthArtifactEval/blob/master/boomerang/examples/synth_examples/symmetric_optician_tests/ 
	 * */
	
	/* extr-acronym */
	public void extrAcronym() throws TimeoutException {
		String CONFERENCE_NAME_REGEX = "[A-Z][a-z]*( [A-Z][a-z]*)*";
		SFA<CharPred, Character> CONFERENCE_NAME = (new SFAprovider(CONFERENCE_NAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba); 
		assertTrue(CONFERENCE_NAME.accepts(lOfS("Principles Of Programming Languages"), ba));
		
		String CONFERENCE_ACRONYM_REGEX = "[A-Z][A-Z]*";
		SFA<CharPred, Character> CONFERENCE_ACRONYM = (new SFAprovider(CONFERENCE_ACRONYM_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(CONFERENCE_ACRONYM.accepts(lOfS("POPL"), ba));
		
		int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        examples.add(new Pair<String, String>("Principles Of Programming Languages", "POPL"));
        examples.add(new Pair<String, String>("Programming Language Design Implementation", "PLDI")); 	// requires 2 examples
        																								// 'and' omitted from PLDI
        
        // ConstraintsTestSymbolic.customConstraintsTest(CONFERENCE_NAME, CONFERENCE_ACRONYM, CONFERENCE_NAME.stateCount(), 1, fraction, examples, CONFERENCE_NAME, false);
        
        ConstraintsTestSymbolic.customConstraintsTest(CONFERENCE_NAME, CONFERENCE_ACRONYM, 1, 1, fraction, examples, null, false);
	}
	
	/* extr_fname-err */
	public void extrFnameErr() throws TimeoutException {
		
	}
	
	/* extr_fname */
	
	public void extrFname() throws TimeoutException {
		String NONEMPTY_DIRECTORY_REGEX = "(([a-zA-Z.\\-\\_][a-zA-Z.\\-\\_]*)/)*([a-zA-Z.\\-\\_][a-zA-Z.\\-\\_]*)";
		SFA<CharPred, Character> NONEMPTY_DIRECTORY = (new SFAprovider(NONEMPTY_DIRECTORY_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		
		
		String LOCALFOLDER_REGEX = "[a-zA-Z.\\\\-\\\\_][a-zA-Z.\\\\-\\\\_]*";
		SFA<CharPred, Character> LOCALFOLDER = (new SFAprovider(LOCALFOLDER_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
	}
	
	/* extr_num */
	public void extrNum() throws TimeoutException {
		String PHONENUMBERHIDDEN_REGEX = "[a-zA-Z\\s]*[0-9][0-9][0-9]-[0-9][0-9][0-9]-[0-9][0-9][0-9][0-9][a-zA-Z\\s]*";
		SFA<CharPred, Character> PHONENUMBERHIDDEN = (new SFAprovider(PHONENUMBERHIDDEN_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(PHONENUMBERHIDDEN.accepts(lOfS("asdfscxv as df415-342-3622 asdfasdf v a"), ba));
		
		String PHONENUMBER_REGEX = "[0-9][0-9][0-9]-[0-9][0-9][0-9]-[0-9][0-9][0-9][0-9]";
		SFA<CharPred, Character> PHONENUMBER = (new SFAprovider(PHONENUMBER_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(PHONENUMBER.accepts(lOfS("415-342-3622"), ba));
		
		int[] fraction = new int[] {1, 1};
        
        List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
        // examples.add(new Pair<String, String>("asdfscxv as df415-342-3622 asdfasdf v a", "415-342-3622"));
        examples.add(new Pair<String, String>("asdf as df415-342-3622 v", "415-342-3622")); 	// smaller example
		
		ConstraintsTestSymbolic.customConstraintsTest(PHONENUMBERHIDDEN, PHONENUMBER, 1, 1, fraction, examples, null, false);
	}
	
	
	/* extr_odds */
	
	
	/* extr_quant */
	
	public void extrQuant() throws TimeoutException {
		String THINGANDAMOUNT_REGEX = "[a-zA-Z\\s]*[0-9][a-zA-Z\\s0-9]*";
		SFA<CharPred, Character> THINGANDAMOUNT = (new SFAprovider(THINGANDAMOUNT_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(THINGANDAMOUNT.accepts(lOfS("hey look we sure have a lot of corn we have 35 OZ"), ba));
		
		String AMOUNT_EXTRACTED_REGEX = "[0-9][a-zA-Z\\s0-9]*";
		SFA<CharPred, Character> AMOUNT_EXTRACTED = (new SFAprovider(AMOUNT_EXTRACTED_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(AMOUNT_EXTRACTED.accepts(lOfS("35 OZ"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
	    examples.add(new Pair<String, String>("hey look we sure have a lot of corn we have 35 OZ", "35 OZ"));
		
		ConstraintsTestSymbolic.customConstraintsTest(THINGANDAMOUNT, AMOUNT_EXTRACTED, 2, 1, fraction, examples, null, false);
	}
	
	
	/* normalize_spaces */
	
	public void normalizeSpaces() throws TimeoutException {
		String NON_NORMALIZED_TEXT_REGEX = "[a-zA-Z0-9]+(\s(\s)*[a-zA-Z0-9]+)*";
		SFA<CharPred, Character> NON_NORMALIZED_TEXT = (new SFAprovider(NON_NORMALIZED_TEXT_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(NON_NORMALIZED_TEXT.accepts(lOfS("Fix     spaces"), ba));
		
		String NORMALIZED_TEXT_REGEX = "[a-zA-Z0-9]+(\s[a-zA-Z0-9]+)*";
		SFA<CharPred, Character> NORMALIZED_TEXT = (new SFAprovider(NORMALIZED_TEXT_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(NORMALIZED_TEXT.accepts(lOfS("Fix spaces"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
	    examples.add(new Pair<String, String>("Fix     spaces", "Fix spaces"));
	    
	    ConstraintsTestSymbolic.customConstraintsTest(NON_NORMALIZED_TEXT, NORMALIZED_TEXT, 2, 1, fraction, examples, null, false);
	}
	
	
	/* normalize_name_position */
	
	public void normalizeNamePosition() throws TimeoutException {
		String ROW_REGEX = "";
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
}
