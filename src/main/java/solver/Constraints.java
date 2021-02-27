package solver;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;

import automata.SFAOperations;
import automata.sfa.SFA;
import automata.sfa.SFAMove;
import theory.BooleanAlgebra;
import theory.characters.CharPred;
import utilities.Pair;
import utilities.Triple;

public class Constraints {
	
	public static Set<Triple<Integer, String, Integer>> mapToTriples(HashMap<Integer, Pair<String, Integer>> transitionsMap) {
		Set<Triple<Integer, String, Integer>> triples = new HashSet<Triple<Integer, String, Integer>>();
		for (Entry<Integer, Pair<String, Integer>> entry : transitionsMap.entrySet()) {
			Triple<Integer, String, Integer> triple = 
					new Triple<Integer, String, Integer>(entry.getKey(), entry.getValue().first, entry.getValue().second);
		}
		
		return triples;
	}
	
	public static HashMap<Integer, Pair<String, Integer>> triplesToMap(Set<Triple<Integer, String, Integer>> triples) {
		HashMap<Integer, Pair<String, Integer>> transitionsMap = new HashMap<Integer, Pair<String, Integer>>();
		
		for (Triple<Integer, String, Integer> triple : triples) {
			Integer key = triple.first;
			if (transitionsMap.containsKey(key)) {
				Pair<String, Integer> currentEntry = transitionsMap.get(key);
				
				// lower cost
				if (triple.third < currentEntry.second) {
					transitionsMap.put(key, new Pair<String, Integer>(triple.second, triple.third));
				}
				
				// prefer shorter string
				if (triple.third == currentEntry.second && triple.second.length() < currentEntry.first.length()) {
					transitionsMap.put(key, new Pair<String, Integer>(triple.second, triple.third));
				}
			}
			else transitionsMap.put(key, new Pair<String, Integer>(triple.second, triple.third));
		}
		
		return transitionsMap;
	}
	
	// TODO: change return type
	public static Collection<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> 
	bestOutputs(SFA<CharPred, Character> source, SFA<CharPred, Character> target, HashMap<Character, Integer> alphabet, 
			BooleanAlgebra<CharPred, Character> ba) throws TimeoutException {
		
		Collection<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> transitions = 
				new HashSet<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>>();
		Collection<Integer> sourceStates = source.getStates();
		Collection<Integer> targetStates = target.getStates();
		
		for (Integer sourceState : sourceStates) {
			for (Integer targetState : targetStates) {
				Collection<SFAMove<CharPred, Character>> sourceTransitions = source.getTransitionsFrom(sourceState);
				
				for (SFAMove<CharPred, Character> sourceTransition : sourceTransitions) {
					Integer sourceTo = sourceTransition.to;
					Character input = sourceTransition.getWitness(ba);
					
					// Pre-insert 
					Set<Triple<Integer, String, Integer>> triples = new HashSet<Triple<Integer, String, Integer>>();
					Set<Triple<Integer, String, Integer>> triplesOld = new HashSet<Triple<Integer, String, Integer>>();
					while (!triples.equals(triplesOld)) {
						triplesOld.clear();
						triplesOld.addAll(triples);
						
						for (Triple<Integer, String, Integer> triple : triplesOld) {
							for (Character output : alphabet.keySet()) {
								Integer targetTo = SFAOperations.getSuccessorState(target, triple.first, output, ba);
								String newString = triple.second + output;
								Integer newCost = triple.third + 1;
								
								triples.add(new Triple<Integer, String, Integer>(targetTo, newString, newCost));
							}
						}
						triples = mapToTriples(triplesToMap(triples));
					}
					
					
					Set<Triple<Integer, String, Integer>> newTriples = new HashSet<Triple<Integer, String, Integer>>();
					
					// To copy or not to copy
					for (Triple<Integer, String, Integer> triple : triples) {
						Integer targetTo = SFAOperations.getSuccessorState(target, triple.first, input, ba);
						String newString = triple.second + input;
						
						newTriples.add(new Triple<Integer, String, Integer>(targetTo, newString, triple.third));
						
						newTriples.add(new Triple<Integer, String, Integer>(triple.first, triple.second, triple.third + 1));
					}
					
					triples.clear();
					triples.addAll(newTriples);
					
					// Modifying the input character 
					for (Character output : alphabet.keySet()) {
						if (output == input) continue;
						
						for (Triple<Integer, String, Integer> triple : newTriples) {
							Integer targetTo = SFAOperations.getSuccessorState(target, triple.first, output, ba);
							String newString = triple.second + output;
							Integer newCost = triple.third + 1;
							
							triples.add(new Triple<Integer, String, Integer>(targetTo, newString, newCost));
						}
					}
					
					// Post-insert
					while (!triples.equals(triplesOld)) {
						triplesOld.clear();
						triplesOld.addAll(triples);
						
						for (Triple<Integer, String, Integer> triple : triplesOld) {
							for (Character output : alphabet.keySet()) {
								Integer targetTo = SFAOperations.getSuccessorState(target, triple.first, output, ba);
								String newString = triple.second + output;
								Integer newCost = triple.third + 1;
								
								triples.add(new Triple<Integer, String, Integer>(targetTo, newString, newCost));
							}
						}
						triples = mapToTriples(triplesToMap(triples));
					}
					
					// Add to transitions
					for (Triple<Integer, String, Integer> triple : triples) {
						if (!source.isFinalState(sourceTo) && target.isFinalState(triple.first)) continue;
						
						Pair<Integer, Integer> sourcePair = new Pair<Integer, Integer>(sourceState, targetState);
						Triple<Character, String, Integer> move = new Triple<Character, String, Integer>(input, triple.second, triple.third);
						Pair<Integer, Integer> targetPair = new Pair<Integer, Integer>(sourceTo, triple.first);
						Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>> newTransition =
								new Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>(sourcePair, move, targetPair);
					}
					
				}
			}
		}
		
		return transitions;
	}
	
	public static void mkInjectiveMap() {
		
	}
	
	
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public static Solver mkConstraints(Context ctx, Solver solver, HashMap<Character, Integer> alphabet, 
			SFA<CharPred, Character> source, SFA<CharPred, Character> target, int numStates, 
			List<Pair<String, String>> ioExamples, BooleanAlgebra<CharPred, Character> ba) throws TimeoutException {
		
		/* int and bool sorts */
		Sort I = ctx.getIntSort();
		Sort B = ctx.getBoolSort();
		
		/* declare d_1 : Q x \Sigma -> \Sigma^o */
		Sort[] argsToD1 = new Sort[]{ I, I };
		FuncDecl<Sort> d1 = ctx.mkFuncDecl("d1", argsToD1, I);
		
		/* declare d_2 : Q x \Sigma -> Q */
		Sort[] argsToD2 = new Sort[]{ I, I };
		FuncDecl<Sort> d2 = ctx.mkFuncDecl("d2", argsToD2, I);
		
		/* declare x : Q_R x Q x Q_T -> {1, 0} */
		Sort[] argsToX = new Sort[]{ I, I, I };
		FuncDecl<Sort> x = ctx.mkFuncDecl("x", argsToX, B);
		
		/* initial states */
		Expr<IntSort> sourceInit = ctx.mkInt(source.getInitialState());
		Expr<IntSort> targetInit = ctx.mkInt(target.getInitialState());
		Expr<IntSort> init = ctx.mkInt(0);
		Expr res = x.apply(sourceInit, init, targetInit);
		solver.add(res);
		
		Collection<SFAMove<CharPred, Character>> sourceTransitions = source.getTransitions();
		Collection <SFAMove<CharPred, Character>> targetTransitions = target.getTransitions();
		
		/* x function constraints */
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < numStates; j++) {
				// TODO
			}
		}
		
		/* declare f_R : Q -> {0, 1} */
		FuncDecl<Sort> f_R = ctx.mkFuncDecl("f_R", I, B);
		for (Integer sourceState : source.getFinalStates()) {
			Expr<IntSort> stateInt = ctx.mkInt(sourceState);
			Expr c = f_R.apply(stateInt);
			solver.add(c);
		}
		
		/* declare f_T : Q -> {0, 1} */
		FuncDecl<Sort> f_T = ctx.mkFuncDecl("f_T", I, B);
		for (Integer targetState : target.getFinalStates()) {
			Expr<IntSort> stateInt = ctx.mkInt(targetState);
			Expr c = f_T.apply(stateInt);
			solver.add(c);
		}
		
		/* x(q_R, q, q_T) /\ f_R(q_R) -> f_T(q_T) */
		for (int i = 0; i < numStates; i++) {
			for (Integer sourceState : source.getStates()) {
				for (Integer targetState : target.getStates()) {
					Expr<IntSort> sourceInt = ctx.mkInt(sourceState);
					Expr<IntSort> stateInt = ctx.mkInt(i);
					Expr<IntSort> targetInt = ctx.mkInt(targetState);
					
					Expr exp1 = x.apply(sourceInt, stateInt, targetInt);
					Expr exp2 = f_R.apply(sourceInt);
					Expr antecedent = ctx.mkAnd(exp1, exp2);
					Expr consequent = f_T.apply(targetInt);
					Expr c = ctx.mkImplies(antecedent, consequent);
					solver.add(c);
				}
			}
		}
		
		
		return solver;
	}
}
