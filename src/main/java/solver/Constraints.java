package solver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;

import automata.SFAOperations;
import automata.sfa.SFA;
import automata.sfa.SFAMove;
import strings.EditDistanceStrToStr;
import theory.BooleanAlgebra;
import theory.BooleanAlgebraSubst;
import theory.characters.CharConstant;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import transducers.sft.SFT;
import transducers.sft.SFTInputMove;
import transducers.sft.SFTMove;
import utilities.Pair;
import utilities.Triple;

public class Constraints {
	
	// Fields/instance variables
	Context ctx;
	SFA<CharPred, Character> source; 
	SFA<CharPred, Character> target; 
	Set<Character> alphabet;
	HashMap<Character, Integer> alphabetMap;
	BooleanAlgebraSubst<CharPred, CharFunc, Character> ba;
	
	public Constraints(Context ctx, SFA<CharPred, Character> source, SFA<CharPred, Character> target, HashMap<Character, 
			Integer> alphabetMap, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) {
		this.ctx = ctx;
		this.source = source;
		this.target = target;
		this.alphabet = alphabetMap.keySet();
		this.alphabetMap = alphabetMap;
		this.ba = ba;
	}
	
	public static <A> Set<Triple<A, String, Integer>> mapToTriples(HashMap<A, Pair<String, Integer>> transitionsMap) {
		Set<Triple<A, String, Integer>> triples = new HashSet<Triple<A, String, Integer>>();
		for (Entry<A, Pair<String, Integer>> entry : transitionsMap.entrySet()) {
			Triple<A, String, Integer> triple = 
					new Triple<A, String, Integer>(entry.getKey(), entry.getValue().first, entry.getValue().second);
			triples.add(triple);
		}
		
		return triples;
	}
	
	public static <A> HashMap<A, Pair<String, Integer>> triplesToMap(Set<Triple<A, String, Integer>> triples) {
		HashMap<A, Pair<String, Integer>> transitionsMap = new HashMap<A, Pair<String, Integer>>();
		
		for (Triple<A, String, Integer> triple : triples) {
			A key = triple.first;
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
	
	public Set<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>>
	bestOutputs() throws TimeoutException {
		return bestOutputs(source, target, alphabet, ba);
	}
	
	public static Set<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> 
	bestOutputs(SFA<CharPred, Character> source, SFA<CharPred, Character> target, Set<Character> alphabet, 
			BooleanAlgebra<CharPred, Character> ba) throws TimeoutException {
		
		Set<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> transitions = 
				new HashSet<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>>();
		Collection<Integer> sourceStates = source.getStates();
		Collection<Integer> targetStates = target.getStates();
		
		for (Integer sourceState : sourceStates) {
			for (Integer targetState : targetStates) {
				Collection<SFAMove<CharPred, Character>> sourceTransitions = source.getTransitionsFrom(sourceState);
				
				for (SFAMove<CharPred, Character> sourceTransition : sourceTransitions) {
					Integer sourceTo = sourceTransition.to;
					Character input = sourceTransition.getWitness(ba);
					
					/* Pre-insert */
					Set<Triple<Integer, String, Integer>> triples = new HashSet<Triple<Integer, String, Integer>>();
					triples.add(new Triple<Integer, String, Integer>(targetState, "", 0));
					Set<Triple<Integer, String, Integer>> triplesOld = new HashSet<Triple<Integer, String, Integer>>();
					while (!triples.equals(triplesOld)) {
						triplesOld.clear();
						triplesOld.addAll(triples);
						
						for (Triple<Integer, String, Integer> triple : triplesOld) {
							for (Character output : alphabet) {
								Integer targetTo = SFAOperations.getSuccessorState(target, triple.first, output, ba);
								String newString = triple.second + output;
								Integer newCost = triple.third + 1;
								
								triples.add(new Triple<Integer, String, Integer>(targetTo, newString, newCost));
							}
						}
						triples = mapToTriples(triplesToMap(triples));
					}
					
					Set<Triple<Integer, String, Integer>> newTriples = new HashSet<Triple<Integer, String, Integer>>();
					newTriples.addAll(triples);
					
					/* To copy or not to copy */
					for (Triple<Integer, String, Integer> triple : triples) {
						Integer targetTo = SFAOperations.getSuccessorState(target, triple.first, input, ba);
						String newString = triple.second + input;
						
						newTriples.add(new Triple<Integer, String, Integer>(targetTo, newString, triple.third));
						
						newTriples.add(new Triple<Integer, String, Integer>(triple.first, triple.second, triple.third + 1));
					}
					
					triples.clear();
					triples.addAll(newTriples);
					
					/* Modifying the input character */
					for (Character output : alphabet) {
						if (output == input) continue;
						
						for (Triple<Integer, String, Integer> triple : newTriples) {
							Integer targetTo = SFAOperations.getSuccessorState(target, triple.first, output, ba);
							String newString = triple.second + output;
							Integer newCost = triple.third + 1;
							
							triples.add(new Triple<Integer, String, Integer>(targetTo, newString, newCost));
						}
					}
					
					/* Post-insert */
					while (!triples.equals(triplesOld)) {
						triplesOld.clear();
						triplesOld.addAll(triples);
						
						for (Triple<Integer, String, Integer> triple : triplesOld) {
							for (Character output : alphabet) {
								Integer targetTo = SFAOperations.getSuccessorState(target, triple.first, output, ba);
								String newString = triple.second + output;
								Integer newCost = triple.third + 1;
								
								triples.add(new Triple<Integer, String, Integer>(targetTo, newString, newCost));
							}
						}
						triples = mapToTriples(triplesToMap(triples));
					}
					
					/* Add to transitions */
					for (Triple<Integer, String, Integer> triple : triples) {
						if (!source.isFinalState(sourceTo) && target.isFinalState(triple.first)) continue;
						
						Pair<Integer, Integer> sourcePair = new Pair<Integer, Integer>(sourceState, targetState);
						Triple<Character, String, Integer> move = new Triple<Character, String, Integer>(input, triple.second, triple.third);
						Pair<Integer, Integer> targetPair = new Pair<Integer, Integer>(sourceTo, triple.first);
						Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>> newTransition =
								new Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>(sourcePair, move, targetPair);
						transitions.add(newTransition);
					}
					
				}
			}
		}
		
		return transitions;
	}
	
	public Set<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> 
	bestOutputsExamples(Pair<String, String> ioExample) throws TimeoutException {
		return bestOutputsExamples(source, target, ioExample, ba);
	}
	
	public static Set<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> 
	bestOutputsExamples(SFA<CharPred, Character> source, SFA<CharPred, Character> target, Pair<String, String> ioExample,
			BooleanAlgebra<CharPred, Character> ba) throws TimeoutException {
		Set<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> transitions = 
				new HashSet<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>>();
		
		String inputStr = ioExample.first;
		String outputStr = ioExample.second;
			
		int sourceState = source.getInitialState();
		for (int i = 0; i < inputStr.length(); i++) {
			Character inputChar = inputStr.charAt(i);
			// assumes there is a transition in source for every input char in sequence
			Integer sourceTo = SFAOperations.getSuccessorState(source, sourceState, inputChar, ba);  
				
			for (int j = 0; j <= outputStr.length(); j++) {
				Set<Triple<Integer, String, Integer>> triples = new HashSet<Triple<Integer, String, Integer>>();
				String outputSubstr = outputStr.substring(0, j);
				Integer targetState = SFAOperations.getStateInFA(target, target.getInitialState(), outputSubstr, ba);
					
				String outputRemaining = outputStr.substring(j, outputStr.length());
					
				for (int k = 0; k <= outputRemaining.length(); k++) {
					String outputRemSubstr = outputRemaining.substring(0, k);
					Integer targetTo = SFAOperations.getStateInFA(target, targetState, outputRemSubstr, ba);
					int cost = EditDistanceStrToStr.getEditDistance(String.valueOf(inputChar), outputRemSubstr);
						
						
					triples.add(new Triple<Integer, String, Integer>(targetTo, outputRemSubstr, cost));
				}
				triples = mapToTriples(triplesToMap(triples));
					
				/* Add to transitions */
				for (Triple<Integer, String, Integer> triple : triples) {
					if (!source.isFinalState(sourceTo) && target.isFinalState(triple.first)) continue;
						
					Pair<Integer, Integer> sourcePair = new Pair<Integer, Integer>(sourceState, targetState);
					Triple<Character, String, Integer> move = new Triple<Character, String, Integer>(inputChar, triple.second, triple.third);
					Pair<Integer, Integer> targetPair = new Pair<Integer, Integer>(sourceTo, triple.first);
					Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>> newTransition =
							new Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>(sourcePair, move, targetPair);
					transitions.add(newTransition);
				}
			}
				
			sourceState = sourceTo; // advance
		}
		
		return transitions;
		
	}
	
	
	public static Pair<HashMap<String, Integer>, Integer> mkInjectiveMap(Collection<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> transitions, 
			int fresh) {
		HashMap<String, Integer> outputInjMap = new HashMap<String, Integer>();
		int counter = fresh;
		
		for (Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>> transition : transitions) {
			String outputStr = transition.second.second;
			
			if (outputInjMap.containsKey(outputStr)) continue;
			
			outputInjMap.put(outputStr, counter);
			counter++;
		}
		
		return new Pair<HashMap<String, Integer>, Integer>(outputInjMap, counter);
	}
	
	/*
	 * Reverse injective map
	 */
	public static <A, B> HashMap<B, A> reverseMap(HashMap<A, B> map) { 
		HashMap<B, A> reverseMap = new HashMap<B, A>();
		
		for (A key : map.keySet()) {
			reverseMap.put(map.get(key), key);
		}
		
		return reverseMap;
	}
	
	public SFT<CharPred, CharFunc, Character> mkConstraints(int numStates, List<Pair<String, String>> ioExamples) 
			throws TimeoutException {
		return mkConstraints(ctx, ctx.mkSolver(), alphabetMap, source, target, numStates, ioExamples, ba);
	}
	
	
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public static SFT<CharPred, CharFunc, Character> mkConstraints(Context ctx, Solver solver, HashMap<Character, Integer> alphabet, 
			SFA<CharPred, Character> source, SFA<CharPred, Character> target, int numStates, 
			List<Pair<String, String>> ioExamples, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) throws TimeoutException {
		
		/* int and bool sorts */
		Sort I = ctx.getIntSort();
		Sort B = ctx.getBoolSort();
		
		Expr<IntSort> numStatesInt = ctx.mkInt(numStates);
		Expr<IntSort> alphabetSize = ctx.mkInt(alphabet.size());
		Expr<IntSort> zero = ctx.mkInt(0);
		
		/* declare d_1 : Q x \Sigma -> \Sigma^o */
		Sort[] argsToD1 = new Sort[]{ I, I };
		FuncDecl<Sort> d1 = ctx.mkFuncDecl("d1", argsToD1, I);
		
		/* declare d_2 : Q x \Sigma -> Q */
		Sort[] argsToD2 = new Sort[]{ I, I };
		FuncDecl<Sort> d2 = ctx.mkFuncDecl("d2", argsToD2, I);
		
		/* d_1 range */
		for (int i = 0; i < numStates; i++) {
			for (int a : alphabet.values()) {
				Expr<IntSort> q1 = ctx.mkInt(i);
				Expr<IntSort> input = ctx.mkInt(a);
				Expr d1exp = d1.apply(q1, input);
				Expr d2exp = d2.apply(q1, input);
				Expr c1 = ctx.mkLt(d1exp, alphabetSize);
				Expr c2 = ctx.mkGe(d1exp, zero);
				solver.add(c1);
				solver.add(c2);
				c1 = ctx.mkLt(d2exp, numStatesInt);
				c2 = ctx.mkGe(d2exp, zero);
				solver.add(c1);
				solver.add(c2);
			}
		}
		
		/* declare x : Q_R x Q x Q_T -> {1, 0} */
		Sort[] argsToX = new Sort[]{ I, I, I };
		FuncDecl<Sort> x = ctx.mkFuncDecl("x", argsToX, B);
		
		/* initial states */
		Expr<IntSort> sourceInit = ctx.mkInt(source.getInitialState());
		Expr<IntSort> targetInit = ctx.mkInt(target.getInitialState());
		Expr<IntSort> init = ctx.mkInt(0);
		Expr res = x.apply(sourceInit, init, targetInit);
		solver.add(res);
		
		/* set of finite outputs */
		Set<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> outputs = 
				bestOutputs(source, target, alphabet.keySet(), ba);
		
		
		/* map */
		Pair<HashMap<String, Integer>, Integer> outputMapandFreshCounter = mkInjectiveMap(outputs, 0);
		HashMap<String, Integer> outputMap = outputMapandFreshCounter.first;
		
		/* x function constraints */
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < numStates; j++) {
				for (Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>> transition : outputs) {
					/* pair of source states */
					Pair<Integer, Integer> sourcePair = transition.first;
					Expr<IntSort> qR = ctx.mkInt(sourcePair.first);
					Expr<IntSort> q1 = ctx.mkInt(i);
					Expr<IntSort> qT = ctx.mkInt(sourcePair.second);
					
					Expr x1 = x.apply(qR, q1, qT);
					
					/* pair of target states */
					Pair<Integer, Integer> targetPair = transition.third;
					Expr<IntSort> qRprime = ctx.mkInt(targetPair.first);
					Expr<IntSort> q2 = ctx.mkInt(j);
					Expr<IntSort> qTprime = ctx.mkInt(targetPair.second);
					
					Expr x2 = x.apply(qRprime, q2, qTprime);
					
					/* input */
					Character inputChar = transition.second.first;
					Integer input = alphabet.get(inputChar);
					Expr<IntSort> a = ctx.mkInt(input);
					
					/* output */
					String outputStr = transition.second.second;
					Integer output = outputMap.get(outputStr);
					Expr<IntSort> b = ctx.mkInt(output);
					
					/* d expressions */
					Expr d1exp = d1.apply(q1, a);
					Expr eq1 = ctx.mkEq(d1exp, b);
					
					Expr d2exp = d2.apply(q1, a);
					Expr eq2 = ctx.mkEq(d2exp, q2);
					
					Expr antecedent = ctx.mkAnd(x1, eq1, eq2);
					Expr c = ctx.mkImplies(antecedent, x2);
					solver.add(c);
				}
				
			}
		}
		
		/* declare f_R : Q -> {0, 1} */
		FuncDecl<Sort> f_R = ctx.mkFuncDecl("f_R", I, B);
		for (Integer sourceState : source.getStates()) {
			Expr<IntSort> stateInt = ctx.mkInt(sourceState);
			Expr c = f_R.apply(stateInt);
			if (!source.isFinalState(sourceState)) c = ctx.mkNot(c);
			solver.add(c);
		}
		
		/* declare f_T : Q -> {0, 1} */
		FuncDecl<Sort> f_T = ctx.mkFuncDecl("f_T", I, B);
		for (Integer targetState : target.getStates()) {
			Expr<IntSort> stateInt = ctx.mkInt(targetState);
			Expr c = f_T.apply(stateInt);
			if (!target.isFinalState(targetState)) c = ctx.mkNot(c);
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
		
		/* Input-output examples */
		FuncDecl[] eFuncs = new FuncDecl[ioExamples.size()];
		
		/* Set of all outputs */
		Set<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> allOutputs =
				new HashSet<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>>();
		allOutputs.addAll(outputs);
		
		int exampleCount = 0;
		for (Pair<String, String> ioExample : ioExamples) {
			/* declare function e_k: k x input_position x output_position x Q */
			Sort[] args = new Sort[] { I, I, I };
			eFuncs[exampleCount] = ctx.mkFuncDecl("e " + String.valueOf(exampleCount), args, B);
			FuncDecl e = eFuncs[exampleCount];
			
			/* initial position : e_k(0, 0, q_0) */
			Expr<IntSort> k = ctx.mkInt(exampleCount);
			Expr c = e.apply(zero, zero, zero);
			solver.add(c);
			
			int inputLen = ioExample.first.length();
			Expr<IntSort> inputLength = ctx.mkInt(inputLen);
			int outputLen = ioExample.second.length();
			Expr<IntSort> outputLength = ctx.mkInt(outputLen);
			
			/* final position : e_k(l1, l2, q) \wedge x(q_R, q, q_T) -> f_R(q_R) \wedge f_T(q_T) */
			for (int i = 0; i < numStates; i++) {
				for (Integer sourceState : source.getStates()) {
					for (Integer targetState : target.getStates()) {
						Expr<IntSort> sourceInt = ctx.mkInt(sourceState);
						Expr<IntSort> stateInt = ctx.mkInt(i);
						Expr<IntSort> targetInt = ctx.mkInt(targetState);
						
						Expr exp1 = e.apply(inputLength, outputLength, stateInt);
						Expr exp2 = x.apply(sourceInt, stateInt, targetInt);
						Expr exp3 = f_R.apply(sourceInt);
						Expr exp4 = f_T.apply(targetInt);
						
						Expr antecedent = ctx.mkAnd(exp1, exp2);
						Expr consequent = ctx.mkAnd(exp3, exp4);
						c = ctx.mkImplies(antecedent, consequent);
						solver.add(c);
					}
				}
			}
			
			Set<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> exampleTransitions = 
					bestOutputsExamples(source, target, ioExample, ba);
			
			/* Set of outputs to use for this particular example */
			Set<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>> outputsForExample =
					new HashSet<Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>>>();
			outputsForExample.addAll(outputs);
			outputsForExample.addAll(exampleTransitions);
			
			/* Set of all outputs updated */
			allOutputs.addAll(exampleTransitions);
			
			/*  Expand injective map of all outputs to include new outputs */
			outputMapandFreshCounter = mkInjectiveMap(allOutputs, outputMapandFreshCounter.second);
			outputMap = outputMapandFreshCounter.first;
			
			for (int m = 0; m < numStates; m++) {
				for (int n = 0; n < numStates; n++) {
					for (Triple<Pair<Integer, Integer>, Triple<Character, String, Integer>, Pair<Integer, Integer>> transition : outputsForExample) {
						
						/* pair of source states */
						Pair<Integer, Integer> sourcePair = transition.first;
						Expr<IntSort> qR = ctx.mkInt(sourcePair.first);
						Expr<IntSort> q1 = ctx.mkInt(m);
						Expr<IntSort> qT = ctx.mkInt(sourcePair.second);
						
						Expr x1 = x.apply(qR, q1, qT);
						
						/* pair of target states */
						Pair<Integer, Integer> targetPair = transition.third;
						Expr<IntSort> qRprime = ctx.mkInt(targetPair.first);
						Expr<IntSort> q2 = ctx.mkInt(n);
						Expr<IntSort> qTprime = ctx.mkInt(targetPair.second);
						
						Expr x2 = x.apply(qRprime, q2, qTprime);
						
						/* input */
						Character inputChar = transition.second.first;
						Integer input = alphabet.get(inputChar);
						Expr<IntSort> a = ctx.mkInt(input);
						
						/* output */
						String outputStr = transition.second.second;
						Integer output = outputMap.get(outputStr);
						Expr<IntSort> b = ctx.mkInt(output);
						
						/* d expressions */
						Expr d1exp = d1.apply(q1, a);
						Expr eq1 = ctx.mkEq(d1exp, b);
						
						Expr d2exp = d2.apply(q1, a);
						Expr eq2 = ctx.mkEq(d2exp, q2);
						
						
						/* e expressions using outputsForExample */
						
						/* input positions */
						List<Integer> inputPositions = 
								SFAOperations.getPositionInStr(source, sourcePair.first, ioExample.first, ba);
						
						/* output positions */
						List<Integer> outputPositions = 
								SFAOperations.getPositionInStr(source, sourcePair.second, ioExample.second, ba);
						
						for (Integer i : inputPositions) {
							for (Integer j : outputPositions) {
								Expr<IntSort> inputPos = ctx.mkInt(i);
								Expr<IntSort> outputPos = ctx.mkInt(j);
								Expr e1 = e.apply(inputPos, outputPos, q1);
								
								Expr<IntSort> inputPosNext = ctx.mkInt(i + 1);
								Expr<IntSort> outputPosNext = ctx.mkInt(j + outputStr.length());
								Expr e2 = e.apply(inputPosNext, outputPosNext, q2);
								
								Expr antecedent = ctx.mkAnd(e1, eq1, eq2, x1);
								Expr consequent = ctx.mkAnd(e2, x2);
								Expr exampleConstraint = ctx.mkImplies(antecedent, consequent);
								solver.add(exampleConstraint);
							}
						}
					}
				}
			}
			
			exampleCount++;
		}
		
		
		/* debug */
		boolean debug = false;
		// System.out.println(solver.toString());
		if (debug) { 
			if (solver.check() == Status.SATISFIABLE) {
				Model m = solver.getModel();
				System.out.println(m.getFuncInterp(x));
				System.out.println(m.getFuncInterp(d1));
				System.out.println(m.getFuncInterp(d2));
				
				for (int q1 = 0; q1 < numStates; q1++) {
					for (int a = 0; a < alphabet.size(); a++) {
						Expr q1Int = ctx.mkInt(q1);
						Expr move = ctx.mkInt(a);
						Expr d1exp = d1.apply(q1Int, move);
						Expr d2exp = d2.apply(q1Int, move);	
									
						// System.out.println(q1 + ", " + a + ", " + m.evaluate(d1exp, false));	
					}
				}
			}		
		}
		
		
		/* construct transducer */
		
		/* reverse HashMaps */
		HashMap<Integer, String> reverseOutputMap = reverseMap(outputMap);
		HashMap<Integer, Character> reverseAlphabet = reverseMap(alphabet);
		
		List<SFTMove<CharPred, CharFunc, Character>> transitionsFT = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		
		if (solver.check() == Status.SATISFIABLE) {
			Model m = solver.getModel();
			for (int q1 = 0; q1 < numStates; q1++) {
				for (int a : alphabet.values()) { 
					Character input = reverseAlphabet.get(a);
					Expr q1Int = ctx.mkInt(q1);
					Expr move = ctx.mkInt(a); 
					Expr d1exp = d1.apply(q1Int, move);
					Expr d2exp = d2.apply(q1Int, move);	
								
					/* get output */
					IntNum output = (IntNum) m.evaluate(d1exp, false);
					int outputInt = output.getInt();
					String outputStr = reverseOutputMap.get(outputInt);
					
					List<CharFunc> outputFunc = new ArrayList<CharFunc>();
					for (int l = 0; l < outputStr.length(); l++) {
						char c = outputStr.charAt(l);
						outputFunc.add(new CharConstant(c));
					}
						
					/* get state */
					IntNum successor = (IntNum) m.evaluate(d2exp, false);
					int q2 = successor.getInt();
					
					transitionsFT.add(new SFTInputMove<CharPred, CharFunc, Character>(q1, q2, new CharPred(input), outputFunc));
				}
			}
		}
		
		HashMap<Integer, Set<List<Character>>> finStates = new HashMap<Integer, Set<List<Character>>>();
		SFT<CharPred, CharFunc, Character> mySFT = SFT.MkSFT(transitionsFT, 0, finStates, ba);
		
		return mySFT;
	}
	
}
