package benchmarks;

import automata.sfa.SFA;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import utilities.SFAprovider;

public class StdRegex {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	public final static String LOWERCASE_REGEX = "[a-z]";
	
	public final static String UPPERCASE_REGEX = "[A-Z]";
	
	public final static String DIGIT_REGEX = "[0-9]";
	
	public final static String NUMBER_REGEX = "[0-9][0-9]*";
	public final static SFA<CharPred, Character> NUMBER = (new SFAprovider(NUMBER_REGEX, ba)).getSFA(); 	// w/ epsilon moves
	
	public final static String WSP_REGEX = "\\s";
	
	public final static String WSP_REPEAT_REGEX = "\\s*";
}
