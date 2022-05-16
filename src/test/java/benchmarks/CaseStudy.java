package benchmarks;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.sat4j.specs.TimeoutException;

import automata.sfa.SFA;
import solver.ConstraintsTestSymbolic;
import solver.Driver;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import theory.intervals.UnaryCharIntervalSolver;
import transducers.sft.SFT;
import utilities.Pair;
import utilities.SFAprovider;
import utilities.Triple;

public class CaseStudy {
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	// Synthesize FIRST transducer
	public static void extractFirst() throws TimeoutException, IOException {
		String sourceRegex = "[A-Za-z]*";
		SFA<CharPred, Character> source = (new SFAprovider(sourceRegex, ba)).getSFA().removeEpsilonMoves(ba);
		
		String targetRegex = "[A-Za-z]*";
		SFA<CharPred, Character> target = (new SFAprovider(targetRegex, ba)).getSFA().removeEpsilonMoves(ba);
		
		int[] dist = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("anvay", "A"));
        examples.add(new Pair<String, String>("Loris", "l"));
        
        Triple<Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>>, String> result = 
				Driver.runAlgorithm(source, target, 2, 1, 0, dist, examples, null, null, null, null, null, null);
        
        Pair<SFT<CharPred, CharFunc, Character>, SFT<CharPred, CharFunc, Character>> res1 = result.first;
        System.out.println(res1.first.toDotString(ba));
	}
	
	// TODO: chance the following function to not call ConstraintsTestSymbolic (go through Driver)
	public static void extractLast() throws TimeoutException {
		String sourceRegex = "[A-Za-z]*";
		SFA<CharPred, Character> source = (new SFAprovider(sourceRegex, ba)).getSFA().removeEpsilonMoves(ba);
		
		String targetRegex = "[A-Za-z]*";
		SFA<CharPred, Character> target = (new SFAprovider(targetRegex, ba)).getSFA().removeEpsilonMoves(ba);
		
		int[] dist = new int[] {1, 1};
		
		List<Pair<String, String>> examples = new ArrayList<Pair<String, String>>();
		examples.add(new Pair<String, String>("anvay", "y"));
        examples.add(new Pair<String, String>("grover", "r"));
        examples.add(new Pair<String, String>("x", "x"));
        examples.add(new Pair<String, String>("xy", "y"));
		
		ConstraintsTestSymbolic.customLookaheadConstraintsTest(source, target, 2, 2, 1, dist, examples, null, null, false);
	}
	
	public static void main(String[] args) throws TimeoutException, IOException {
		extractFirst();
		extractLast();
	}
	
}
