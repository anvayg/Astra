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

public class SynthBench {
	
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
	
	/* extr-acronym-2: with lowercase 'of' */
	
	public void extrAcronym2() throws TimeoutException {
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
        
        ConstraintsTestSymbolic.customConstraintsTest(CONFERENCE_NAME, CONFERENCE_ACRONYM, 2, 1, fraction, examples, null, false);
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
	
	public void extrOdds() throws TimeoutException {
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
	    examples.add(new Pair<String, String>("(142/12)()21", "(142/12)#"));
	    examples.add(new Pair<String, String>("5()(70/8)()21", "(70/8)#"));
		
		ConstraintsTestSymbolic.customConstraintsTest(UNCLEANED_DATA, CLEANEDODDS, 3, 2, fraction, examples, null, false);
	}
	
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
	
	public void normalizeNamePosition() throws TimeoutException {	// modified
		String ROW_REGEX = "NAME: ([A-Z][a-z]*) TITLE: ([A-Z][a-z]*)";
		SFA<CharPred, Character> ROW = (new SFAprovider(ROW_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(ROW.accepts(lOfS("NAME: Alex TITLE: Asst"), ba));
		
		String TITLED_NAME_REGEX = "([A-Z][a-z]*)[(]([A-Z][a-z]*)[)]";
		SFA<CharPred, Character> TITLED_NAME = (new SFAprovider(TITLED_NAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(TITLED_NAME.accepts(lOfS("Alex(Asst)"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("NAME: Ben TITLE: Mr", "Ben(Mr)"));
		examples.add(new Pair<String, String>("NAME: H TITLE: Dr", "H(Dr)"));
	    examples.add(new Pair<String, String>("NAME: Alex TITLE: Asst", "Alex(Asst)"));  // omitted examples, 
	    																				// because we can't remember things
	    
	    ConstraintsTestSymbolic.customConstraintsTest(ROW, TITLED_NAME, 3, 2, fraction, examples, null, false);
	}
	
	/* cap-prob */
	
	public void capProb() throws TimeoutException {
		String UPPERCASENAME_REGEX = "[A-Z][A-Z]*";
		SFA<CharPred, Character> UPPERCASENAME = (new SFAprovider(UPPERCASENAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(UPPERCASENAME.accepts(lOfS("DOE"), ba));
		
		String NAME_REGEX = "[A-Z][a-z]*";
		SFA<CharPred, Character> NAME = (new SFAprovider(NAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(NAME.accepts(lOfS("Doe"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
	    examples.add(new Pair<String, String>("DOE", "Doe"));
	    examples.add(new Pair<String, String>("ODE", "Ode"));
	    
	    ConstraintsTestSymbolic.customConstraintsTest(UPPERCASENAME, NAME, 2, 1, fraction, examples, null, false);
	}
	
	/* remove-last */
	
	public void removeLast() throws TimeoutException {
		String FIRSTLASTNAME_REGEX = "[A-Z][a-z]* [A-Z][a-z]*";
		SFA<CharPred, Character> FIRSTLASTNAME = (new SFAprovider(FIRSTLASTNAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(FIRSTLASTNAME.accepts(lOfS("John Doe"), ba));
		
		String NAME_REGEX = "[A-Z][a-z]*";
		SFA<CharPred, Character> NAME = (new SFAprovider(NAME_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(NAME.accepts(lOfS("John"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
	    examples.add(new Pair<String, String>("John Doe", "John"));
	    examples.add(new Pair<String, String>("Anvay Grover", "Anvay"));
	    
	    ConstraintsTestSymbolic.customConstraintsTest(FIRSTLASTNAME, NAME, 2, 1, fraction, examples, null, false);
	}
	
	/* title-converter */
	
	public void titleConverter() throws TimeoutException {
		String TITLE_LEGACY_REGEX = "<Field Id=1>[a-zA-Z\\s0-9]*</Field>";
		SFA<CharPred, Character> TITLE_LEGACY = (new SFAprovider(TITLE_LEGACY_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(TITLE_LEGACY.accepts(lOfS("<Field Id=1>ti</Field>"), ba));
		
		String TITLE_MODERN_REGEX = "\"title\"=\"[a-zA-Z\\s0-9][a-zA-Z\\s0-9]*\"";
		SFA<CharPred, Character> TITLE_MODERN = (new SFAprovider(TITLE_MODERN_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(TITLE_MODERN.accepts(lOfS("\"title\"=\"ti\""), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("<Field Id=1>title</Field>", "\"title\"=\"title\""));
		
		ConstraintsTestSymbolic.customConstraintsTest(TITLE_LEGACY, TITLE_MODERN, 3, 1, fraction, examples, null, false);
	}
	
	/* bibtex-to-readable-title */
	
	public void bibtexToReadableTitle() throws TimeoutException {
		String BIBTEX_TITLE_REGEX = "title=[{]([A-Z][a-z]*)(\\s[A-Z][a-z]*)*[}]";
		SFA<CharPred, Character> BIBTEX_TITLE = (new SFAprovider(BIBTEX_TITLE_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(BIBTEX_TITLE.accepts(lOfS("title={Boomerang Resourceful Lenses For String Data}"), ba));
		
		String READABLE_TITLE_REGEX = "ti - ([A-Z][a-z]*)(\\s[A-Z][a-z]*)*";
		SFA<CharPred, Character> READABLE_TITLE = (new SFAprovider(READABLE_TITLE_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(READABLE_TITLE.accepts(lOfS("ti - Boomerang Resourceful Lenses For String Data"), ba));
		
		int[] fraction = new int[] {3, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("title={Boom}", "ti - Boom"));
		examples.add(new Pair<String, String>("title={Lenses}", "ti - Lenses"));
		
		ConstraintsTestSymbolic.customConstraintsTest(BIBTEX_TITLE, READABLE_TITLE, 5, 1, fraction, examples, null, false);
	}
	
	/* Bommerang_composers: source_to_views */
	
	public void sourceToViews() throws TimeoutException {
		String SOURCE_REGEX = "([A-Za-z\\s]+[,] [0-9]{4}[-][0-9]{4}[,] [A-Za-z\\s]+)";
		SFA<CharPred, Character> SOURCE = (new SFAprovider(SOURCE_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		System.out.println(SFAOperations.getStateInFA(SOURCE, SOURCE.getInitialState(), "Jean Sibelius, 1865-1957, Finnish", ba));
		System.out.println(SOURCE.getFinalStates());
		assertTrue(SOURCE.accepts(lOfS("Jean Sibelius, 1865-1957, Finnish"), ba));
		
		String VIEW_REGEX = "([A-Za-z\\s]+[,] [A-Za-z\\s]+)";
		SFA<CharPred, Character> VIEW = (new SFAprovider(VIEW_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(VIEW.accepts(lOfS("Jean Sibelius, Finnish"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("Jean Sibelius, 1865-1957, Finnish", "Jean Sibelius, Finnish"));
		examples.add(new Pair<String, String>("Jean, 1865-1957, Finnish", "Jean, Finnish"));
		
		ConstraintsTestSymbolic.customConstraintsTest(SOURCE, VIEW, 3, 1, fraction, examples, null, false);
	}
	
	/* DOS-to-Unix line endings */
	
	public void dosToUnix() throws TimeoutException {
		String DOS_REGEX = "[A-Za-z0-9]*(\\r\\n[A-Za-z0-9]*)*";
		SFA<CharPred, Character> DOS = (new SFAprovider(DOS_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(DOS.accepts(lOfS("a\r\na"), ba));
		
		String UNIX_REGEX = "[A-Za-z0-9]*(\\n[A-Za-z0-9]*)*";
		SFA<CharPred, Character> UNIX = (new SFAprovider(UNIX_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(UNIX.accepts(lOfS("a\na"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("abc", "abc"));
		examples.add(new Pair<String, String>("\r\n", "\n"));
        
        ConstraintsTestSymbolic.customConstraintsTest(DOS, UNIX, 2, 1, fraction, examples, null, false);
	}
	
	/* Unix-to-DOS line endings */
	
	public void unixToDos() throws TimeoutException {
		String DOS_REGEX = "[A-Za-z0-9]*(\\r\\n[A-Za-z0-9]*)*";
		SFA<CharPred, Character> DOS = (new SFAprovider(DOS_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		
		String UNIX_REGEX = "[A-Za-z0-9]*(\\n[A-Za-z0-9]*)*";
		SFA<CharPred, Character> UNIX = (new SFAprovider(UNIX_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("abc", "abc"));
        examples.add(new Pair<String, String>("\n", "\r\n"));
        
        ConstraintsTestSymbolic.customConstraintsTest(UNIX, DOS, 2, 2, fraction, examples, null, false);
	}
	
	/* CSV separator conversion */
	
	public void changeCSV() throws TimeoutException {
		String DOT_REGEX = "[A-Za-z0-9]*([.] [A-Za-z0-9]*)*";
		SFA<CharPred, Character> DOT = (new SFAprovider(DOT_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		
		String COMMA_REGEX = "[A-Za-z0-9]*([,] [A-Za-z0-9]*)*";
		SFA<CharPred, Character> COMMA = (new SFAprovider(COMMA_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("a. b", "a, b"));
		
		ConstraintsTestSymbolic.customConstraintsTest(DOT, COMMA, 1, 1, fraction, examples, null, false);
	}
	
	@Test
	public void formatPhoneNumber() throws TimeoutException {
		String NUMBER_REGEX = "[0-9]{10}";
		SFA<CharPred, Character> NUMBER = (new SFAprovider(NUMBER_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(NUMBER.accepts(lOfS("6757925603"), ba));
		
		String NUMBER_FORMATTED_REGEX = "[0-9]{3}[-][0-9]{3}[-][0-9]{4}";
		SFA<CharPred, Character> NUMBER_FORMATTED = (new SFAprovider(NUMBER_FORMATTED_REGEX, ba)).getSFA().removeEpsilonMoves(ba);
		assertTrue(NUMBER_FORMATTED.accepts(lOfS("675-792-5603"), ba));
		
		int[] fraction = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("6757925603", "675-792-5603"));
		
		ConstraintsTestSymbolic.customConstraintsTest(NUMBER, NUMBER_FORMATTED, 4, 2, fraction, examples, null, false);
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
