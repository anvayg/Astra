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
        
        ConstraintsTestSymbolic.customConstraintsTest(CONFERENCE_NAME, CONFERENCE_ACRONYM, CONFERENCE_NAME.stateCount(), 1, fraction, examples, CONFERENCE_NAME, false);
        
        ConstraintsTestSymbolic.customConstraintsTest(CONFERENCE_NAME, CONFERENCE_ACRONYM, 1, 1, fraction, examples, null, false);
	}
	
	/* extr_fname-err */
	public void extrFnameErr() throws TimeoutException {
		
	}
	
	/* extr_fname */
	@Test
	public void extrFname() throws TimeoutException {
		String NONEMPTY_DIRECTORY_REGEX = "(([a-zA-Z.\\-\\_][a-zA-Z.\\-\\_]*)/)*([a-zA-Z.\\-\\_][a-zA-Z.\\-\\_]*)";
		SFA<CharPred, Character> NONEMPTY_DIRECTORY = (new SFAprovider(NONEMPTY_DIRECTORY_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		System.out.println(NONEMPTY_DIRECTORY.toDotString(ba));
		
		String LOCALFOLDER_REGEX = "[a-zA-Z.\\\\-\\\\_][a-zA-Z.\\\\-\\\\_]*";
		SFA<CharPred, Character> LOCALFOLDER = (new SFAprovider(LOCALFOLDER_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		
		
	}
	
	/* extr_num */
	@Test
	public void extrNum() throws TimeoutException {
		
	}
	
	
	/* extr_odds */
	
	
	/* extr_quant */
	
	
	/* normalize_spaces */
	
	
	/* normalize_name_position */
	
	
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
