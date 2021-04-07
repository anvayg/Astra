package solver;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;

import automata.SFAOperations;
import automata.sfa.SFA;
import automata.sfa.SFAMove;
import theory.BooleanAlgebraSubst;
import theory.characters.CharConstant;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import transducers.sft.SFT;
import transducers.sft.SFTInputMove;
import transducers.sft.SFTMove;
import utilities.Pair;

public class Constraints {
	
	/* Fields/instance variables */
	Context ctx;
	SFA<CharPred, Character> source; 
	SFA<CharPred, Character> target; 
	Set<Character> alphabet;
	HashMap<Character, Integer> alphabetMap;
	BooleanAlgebraSubst<CharPred, CharFunc, Character> ba;
		
	/* Constructor */
	public Constraints(Context ctx, SFA<CharPred, Character> source, SFA<CharPred, Character> target, HashMap<Character, 
				Integer> alphabetMap, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) {
		this.ctx = ctx;
		this.source = source;
		this.target = target;
		this.alphabet = alphabetMap.keySet();
		this.alphabetMap = alphabetMap;
		this.ba = ba;
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
	
	/* 
	 * Converts a string from an input-output example to an int array using the alphabet map
	 */
	public static int[] stringToIntArray(HashMap<Character, Integer> alphabetMap, String str) {
		int[] arr = new int[str.length()];
		
		for (int i = 0; i < str.length(); i++) {
			arr[i] = alphabetMap.get(str.charAt(i));
		}
		
		return arr;
	}
	
	/* static method for mkConstraints without examples */
	public SFT<CharPred, CharFunc, Character> mkConstraints(int numStates, int bound, 
			int[] fraction, boolean debug) throws TimeoutException {
		List<Pair<String, String>> empty = new ArrayList<Pair<String, String>>();
		return mkConstraints(ctx, ctx.mkSolver(), alphabetMap, source, target, numStates, bound, fraction, empty, ba, debug);
	}
	
	/* static method for mkConstraints */
	public SFT<CharPred, CharFunc, Character> mkConstraints(int numStates, int bound, int[] fraction, 
			List<Pair<String, String>> ioExamples, boolean debug) throws TimeoutException { 	// take out debug later
		return mkConstraints(ctx, ctx.mkSolver(), alphabetMap, source, target, numStates, bound, fraction, ioExamples, ba, debug);
	}
		
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public static SFT<CharPred, CharFunc, Character> mkConstraints(Context ctx, Solver solver, HashMap<Character, Integer> alphabetMap, 
			SFA<CharPred, Character> source, SFA<CharPred, Character> target, int numStates, int length, int[] fraction, 
			List<Pair<String, String>> ioExamples, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba, 
			boolean debug) throws TimeoutException {
		
		/* int and bool sorts */
		Sort I = ctx.getIntSort();
		Sort B = ctx.getBoolSort();
		
		Expr<IntSort> numStatesInt = ctx.mkInt(numStates);
		Expr<IntSort> alphabetSize = ctx.mkInt(alphabetMap.size());
		Expr<IntSort> zero = ctx.mkInt(0);
		Expr<IntSort> bound = ctx.mkInt(length);
		
		/* declare d_1:  */
		Sort[] argsToD1 = new Sort[]{ I, I, I };
		FuncDecl<Sort> d1 = ctx.mkFuncDecl("d1", argsToD1, I);
		
		/* declare out_len */
		Sort[] argsToOutLen = new Sort[]{ I, I };
		FuncDecl<Sort> out_len = ctx.mkFuncDecl("out_len", argsToOutLen, I);
		
		/* declare d_2 : Q x \Sigma -> Q */
		Sort[] argsToD2 = new Sort[]{ I, I };
		FuncDecl<Sort> d2 = ctx.mkFuncDecl("d2", argsToD2, I);
		
		/* declare x : Q_R x Q x Q_T -> {1, 0} */
		Sort[] argsToX = new Sort[]{ I, I, I };
		FuncDecl<Sort> x = ctx.mkFuncDecl("x", argsToX, B);
		
		/* initial states: x(q^0_R, q^0, q^0_T) */
		Expr<IntSort> sourceInit = ctx.mkInt(source.getInitialState());
		Expr<IntSort> targetInit = ctx.mkInt(target.getInitialState());
		Expr res = x.apply(sourceInit, zero, targetInit);
		solver.add(res);
		
		/* d_R: transition relation of source */
		Sort[] argsToDR = new Sort[]{ I, I };
		FuncDecl<Sort> dR = ctx.mkFuncDecl("dR", argsToDR, I);
		
		/* encode d_R */
		Collection<SFAMove<CharPred, Character>> sourceTransitions = source.getTransitions();
		for (SFAMove<CharPred, Character> transition : sourceTransitions) {
			Integer stateFrom = transition.from;
			Expr<IntSort> q1 = ctx.mkInt(stateFrom);
			
			Character move = transition.getWitness(ba); // there should only be 1
			Expr<IntSort> a = ctx.mkInt(alphabetMap.get(move));
			
			Integer stateTo = transition.to;
			Expr<IntSort> q2 = ctx.mkInt(stateTo);
			
			Expr dexp = dR.apply(q1, a);
			solver.add(ctx.mkEq(dexp, q2));
		}
		
		/* d_T: transition relation of target */
		Sort[] argsToDT = new Sort[]{ I, I };
		FuncDecl<Sort> dT = ctx.mkFuncDecl("dT", argsToDT, I);
		
		/* encode d_T */
		Collection<SFAMove<CharPred, Character>> targetTransitions = target.getTransitions();
		for (SFAMove<CharPred, Character> transition : targetTransitions) {
			Integer stateFrom = transition.from;
			Expr<IntSort> q1 = ctx.mkInt(stateFrom);
			
			Character move = transition.getWitness(ba); // there should only be 1
			Expr<IntSort> a = ctx.mkInt(alphabetMap.get(move));
			
			Integer stateTo = transition.to;
			Expr<IntSort> q2 = ctx.mkInt(stateTo);
			
			Expr dexp = dT.apply(q1, a);
			solver.add(ctx.mkEq(dexp, q2));
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
		
		for (int i = 0; i < numStates; i++) {	// q 
			Expr<IntSort> q = ctx.mkInt(i);
				
			for (SFAMove<CharPred, Character> sourceTransition : sourceTransitions) {
				Integer stateFrom = sourceTransition.from;
				Character move = sourceTransition.getWitness(ba);
				Expr<IntSort> qR = ctx.mkInt(stateFrom);
				Expr<IntSort> a = ctx.mkInt(alphabetMap.get(move));
				
				/* 0 <= out_len(q, a) <= l; range only needs to be encoded once */
				Expr outLenExpr = out_len.apply(q, a);
				solver.add(ctx.mkLe(zero, outLenExpr));
				solver.add(ctx.mkLe(outLenExpr, bound));
					
				/* make variable q_R' = d_R(q_R, a), the equality is already encoded */
				Expr qRPrime = dR.apply(qR, a);
				
				
				/* make variable q' = d2(q, a) */
				Expr qPrime = d2.apply(q, a);
				
				/* 0 <= qPrime < numStates; range only needs to be encoded once */
				solver.add(ctx.mkLe(zero, qPrime));
				solver.add(ctx.mkLt(qPrime, numStatesInt));
							
				
				/* c_0 = d1(q, a, 0), c_1 = d1(q, a, 1), ..., c_{l-1} = d1(q, a, l-1) */
				
				/* make array of output chars */
				Expr[] outputChars = new Expr[length];
				
				for (int l = 0; l < length; l++) {
					Expr<IntSort> index = ctx.mkInt(l);
					Expr d1exp = d1.apply(q, a, index);
					outputChars[l] = d1exp;
					
					/* 0 <= d1(q, a, index) < alphabetSize */
					solver.add(ctx.mkLe(zero, d1exp));
					solver.add(ctx.mkLt(d1exp, alphabetSize)); 
				}

				
				for (Integer targetFrom : target.getStates()) {
					Expr<IntSort> qT = ctx.mkInt(targetFrom);
					
					
					/* q1 = dT(qT, c0), q2 = dT(q1, c1), ..., q_l = dT(q_{l-1}, c_{l-1}) */
					
					/* make array of destination states in target */
					Expr[] dstStates = new Expr[length];
					
					dstStates[0] = dT.apply(qT, outputChars[0]);
					for (int l = 1; l < length; l++) { 		// start from 1 in the loop
						dstStates[l] = dT.apply(dstStates[l - 1], outputChars[l]); // changed to l from l-1
					}
					
					
					/* x(q_R, q, q_T) */
					Expr xExpr = x.apply(qR, q, qT);
		
					
					/* expressions for implications: out_len(q, a) = 0 ==> x(qR', q', qT) */
					
					/* special case for 0 */
					Expr lenEq = ctx.mkEq(outLenExpr, zero);
					Expr xExprPrime = x.apply(qRPrime, qPrime, qT);
					Expr c = ctx.mkImplies(lenEq, xExprPrime);
					
					/* loop for the rest */
					Expr consequent = c;
					for (int l = 0; l < length; l++) {
						int outputLength = l + 1;
						lenEq = ctx.mkEq(outLenExpr, ctx.mkInt(outputLength));
						xExprPrime = x.apply(qRPrime, qPrime, dstStates[l]);
						c = ctx.mkImplies(lenEq, xExprPrime);
						consequent = ctx.mkAnd(consequent, c);
					}
					
					/* make big constraint */
					solver.add(ctx.mkImplies(xExpr, consequent));
				}
			}
		}
		
		
		/* cost constraints */
		
		/* declare C: Q -> Z */
		Sort[] argsToC = new Sort[]{ I };
		FuncDecl energy = ctx.mkFuncDecl("C", argsToC, I);
		
		/* C(0) = 0 */
		// solver.add(ctx.mkEq(energy.apply(zero), zero));
		
		/* declare edit-dist: Q x \Sigma -> Z */
		Sort[] argsToEd = new Sort[]{ I, I };
		FuncDecl<Sort> edDist = ctx.mkFuncDecl("ed_dist", argsToEd, I);
		
		for (int i = 0; i < numStates; i++) {	// q 
			Expr<IntSort> q = ctx.mkInt(i);
				
			for (SFAMove<CharPred, Character> sourceTransition : sourceTransitions) {
				Integer stateFrom = sourceTransition.from;
				Character move = sourceTransition.getWitness(ba);
				Expr<IntSort> qR = ctx.mkInt(stateFrom);
				Expr<IntSort> a = ctx.mkInt(alphabetMap.get(move));
				
				/* make variable out_len(q, a) */
				Expr outLenExpr = out_len.apply(q, a);
					
				/* make variable q_R' = d_R(q_R, a), the equality is already encoded */
				Expr qRPrime = dR.apply(qR, a);
				
				/* make variable q' = d2(q, a) */
				Expr qPrime = d2.apply(q, a);
				
				/* make variable ed_dist(q, a) */
				Expr edDistExpr = edDist.apply(q, a);
				
				/* c_0 = d1(q, a, 0), c_1 = d1(q, a, 1), ..., c_{l-1} = d1(q, a, l-1) */
				
				/* make array of output chars */
				Expr[] outputChars = new Expr[length];
				
				/* comparing a to each output char */
				Expr disjunct = ctx.mkFalse();
				
				for (int l = 0; l < length; l++) {
					Expr<IntSort> index = ctx.mkInt(l);
					Expr d1exp = d1.apply(q, a, index);
					outputChars[l] = d1exp;
					Expr eq = ctx.mkEq(a, d1exp);
					disjunct = ctx.mkOr(disjunct, eq);
				}

				/* for condition where the output chars don't include 'a' */
				Expr negDisjunct = ctx.mkNot(disjunct);
				
				/* (k = 0) ==> ed_dist(q, a) = 1 */
				Expr lenEq = ctx.mkEq(outLenExpr, zero);
				Expr edDistEqOne = ctx.mkEq(edDistExpr, ctx.mkInt(1));
				Expr impl1 = ctx.mkImplies(lenEq, edDistEqOne);
				
				/* \neg (k = 0) ==> ed_dist(q, a) = k - 1 */
				Expr lenNotZero = ctx.mkNot(lenEq);
				Expr edDistKMinus1 = ctx.mkEq(edDistExpr, ctx.mkSub(outLenExpr, ctx.mkInt(1))); 	// check mkSub
				Expr impl2 = ctx.mkImplies(lenNotZero, edDistKMinus1);
				
				/* \neg (k = 0) ==> ed_dist(q, a) = k */
				Expr edDistK = ctx.mkEq(edDistExpr, outLenExpr); 
				Expr impl3 = ctx.mkImplies(lenNotZero, edDistK);
				
				/* energy: C(q) >= C(d2(q, a)) + (m - (n x ed_dist(q, a))) */
				Expr cQ = energy.apply(q);
				Expr cQPrime = energy.apply(qPrime);
				Expr<IntSort> m = ctx.mkInt(fraction[0]);
				Expr<IntSort> n = ctx.mkInt(fraction[1]);
				Expr diff = ctx.mkSub(m, ctx.mkMul(n, edDistExpr));
				Expr c = ctx.mkGe(cQ, ctx.mkAdd(cQPrime, diff));
				// solver.add(c); 
				
				for (Integer targetFrom : target.getStates()) {
					Expr<IntSort> qT = ctx.mkInt(targetFrom);
					
					/* x(q_R, q, q_T) */
					Expr xExpr = x.apply(qR, q, qT);
					
					/* ed_dist constraint 1 */
					Expr antecedent = ctx.mkAnd(xExpr, disjunct);
					Expr consequent = ctx.mkAnd(impl1, impl2);
					// solver.add(ctx.mkImplies(antecedent, consequent));
					
					/* ed_dist constraint 2 */
					antecedent = ctx.mkAnd(xExpr, negDisjunct);
					consequent = ctx.mkAnd(impl1, impl3);
					// solver.add(ctx.mkImplies(antecedent, consequent)); 
				}
				
			}
		}
		
		
		
		/* example constraints */
		FuncDecl[] eFuncs = new FuncDecl[ioExamples.size()];
		
		int exampleCount = 0;
		for (Pair<String, String> ioExample : ioExamples) {
			/* verify example */
			if (!SFAOperations.isAcceptedBy(ioExample.first, source, ba)) throw new IllegalArgumentException();
			if (!SFAOperations.isAcceptedBy(ioExample.second, target, ba)) throw new IllegalArgumentException();
			
			int[] inputArr = stringToIntArray(alphabetMap, ioExample.first);
			int[] outputArr = stringToIntArray(alphabetMap, ioExample.second);
			
			/* declare function e_k: k x input_position x output_position x Q */
			Sort[] args = new Sort[] { I, I, I };
			eFuncs[exampleCount] = ctx.mkFuncDecl("e " + String.valueOf(exampleCount), args, B);
			FuncDecl e = eFuncs[exampleCount];
			
			/* initial position : e_k(0, 0, q_0) */
			solver.add(e.apply(zero, zero, zero));
			
			int inputLen = ioExample.first.length();
			Expr<IntSort> inputLength = ctx.mkInt(inputLen);
			int outputLen = ioExample.second.length();
			Expr<IntSort> outputLength = ctx.mkInt(outputLen);
			
			/* final position : \bigvee_{q \in Q} e_k(l1, l2, q) \wedge x(q_R, q, q_T) \wedge f_R(q_R) \wedge f_T(q_T) */
			Expr bigOr = ctx.mkFalse();
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
						
						Expr c = ctx.mkAnd(exp1, exp2, exp3, exp4);
						bigOr = ctx.mkOr(bigOr, c);
					}
				}
			}
			solver.add(bigOr);
			
			/* not e(l1, l, q) where l < l2 */
			for (int i = 0; i < numStates; i++) {
					Expr<IntSort> stateInt = ctx.mkInt(i);
						
					for (int l = 0; l < outputLen; l++) {
						Expr c = ctx.mkNot(e.apply(inputLength, ctx.mkInt(l), stateInt));
						solver.add(c); 	
					}
			}
	
			
			for (int n = 0; n < numStates; n++) {	// q 
				Expr<IntSort> q = ctx.mkInt(n);
					
				for (SFAMove<CharPred, Character> sourceTransition : sourceTransitions) {
					Integer stateFrom = sourceTransition.from;
					Character move = sourceTransition.getWitness(ba);
					Expr<IntSort> qR = ctx.mkInt(stateFrom);
					Expr<IntSort> a = ctx.mkInt(alphabetMap.get(move));
					
					/* out_len(q, a) */
					Expr outLenExpr = out_len.apply(q, a);
						
					/* make variable q_R' = d_R(q_R, a), the equality is already encoded */
					Expr qRPrime = dR.apply(qR, a);
					
					
					/* make variable q' = d2(q, a) */
					Expr qPrime = d2.apply(q, a);
								
					
					/* c_0 = d1(q, a, 0), c_1 = d1(q, a, 1), ..., c_{l-1} = d1(q, a, l-1) */
					
					/* make array of output chars */
					Expr[] outputChars = new Expr[length];
					
					for (int l = 0; l < length; l++) {
						Expr<IntSort> index = ctx.mkInt(l);
						Expr d1exp = d1.apply(q, a, index);
						outputChars[l] = d1exp;
					}
					
					for (Integer targetFrom : target.getStates()) {
						Expr<IntSort> qT = ctx.mkInt(targetFrom);
						
						/* q1 = dT(qT, c0), q2 = dT(q1, c1), ..., q_l = dT(q_{l-1}, c_{l-1}) */
						
						/* make array of destination states in target */
						Expr[] dstStates = new Expr[length];
						
						dstStates[0] = dT.apply(qT, outputChars[0]);
						for (int l = 1; l < length; l++) { 		// start from 1 in the loop
							dstStates[l] = dT.apply(dstStates[l - 1], outputChars[l]);
						}
						
						/* x(q_R, q, q_T) */
						Expr xExpr = x.apply(qR, q, qT);
						
						for (int i = 0; i < inputLen; i++) { 	// rationale: always read an input character, it's fine to have transition that reads last input char, 
							for (int j = 0; j <= outputLen; j++) {	// but output is already completely generated
								Expr<IntSort> inputPosition = ctx.mkInt(i);
								Expr<IntSort> outputPosition = ctx.mkInt(j);
								
								/* input[i+1] = a */
								Expr nextInputPosition = ctx.mkInt(inputArr[i]);
								Expr inputEq = ctx.mkEq(nextInputPosition, a);
								
								/* output needs be <= outputLen - j */
								int possibleOutputLen = Math.min(outputLen - j, length);
								Expr possibleOutputLength = ctx.mkInt(possibleOutputLen);
								
								Expr outputLe = ctx.mkLe(outLenExpr, possibleOutputLength);
								
								/* e_k(i, j, q) */ 
								Expr eExpr = e.apply(inputPosition, outputPosition, q);
								
								/* expressions for implications: out_len(q, a) = 0 ==> e_k(i+1, j, q') \wedge x(qR', q', qT) */
								
								/* special case for 0 */
								Expr lenEq = ctx.mkEq(outLenExpr, zero);
								Expr eExprPrime = e.apply(ctx.mkInt(i + 1), outputPosition, qPrime);
								Expr xExprPrime = x.apply(qRPrime, qPrime, qT);
								Expr c = ctx.mkIff(ctx.mkAnd(lenEq, inputEq), ctx.mkAnd(eExprPrime, xExprPrime));
//								Expr c = ctx.mkAnd(ctx.mkIff(lenEq, eExprPrime), 
//										ctx.mkIff(lenEq, xExprPrime));
								
								/* loop for the rest */
								Expr consequent = ctx.mkAnd(outputLe, c);
								for (int l = 0; l < possibleOutputLen; l++) { 
									int outputGenLength = l + 1;
									lenEq = ctx.mkEq(outLenExpr, ctx.mkInt(outputGenLength));
									eExprPrime = e.apply(ctx.mkInt(i + 1), ctx.mkInt(j + outputGenLength), qPrime);
									xExprPrime = x.apply(qRPrime, qPrime, dstStates[l]);
									
									/* equalities */
									Expr stringEqualities = ctx.mkTrue();
									for (int inc = 1; inc <= outputGenLength; inc++) {
										int index = (j + inc) - 1;
										Expr nextPosition = ctx.mkInt(outputArr[index]);
										Expr eq = ctx.mkEq(nextPosition, outputChars[inc - 1]); 	// not sure about this
										stringEqualities = ctx.mkAnd(stringEqualities, eq);
									}
									
									c = ctx.mkIff(ctx.mkAnd(lenEq, inputEq), ctx.mkAnd(stringEqualities, eExprPrime, xExprPrime)); 
//									c = ctx.mkAnd(ctx.mkIff(lenEq, stringEqualities), 
//											ctx.mkIff(lenEq, eExprPrime), 
//											ctx.mkIff(lenEq, xExprPrime));
									consequent = ctx.mkAnd(consequent, c);
								}
								
								
								/* make big constraint */
								Expr antecedent = ctx.mkAnd(eExpr, xExpr);
								solver.add(ctx.mkImplies(antecedent, consequent));
							}
						}
						
					}
					
				}
			}
			exampleCount++;
		}
		
		
		/* Reconstruct transducer */
		
		HashMap<Integer, Character> revAlphabetMap = reverseMap(alphabetMap);
		
		List<SFTMove<CharPred, CharFunc, Character>> transitionsFT = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		
		if (solver.check() == Status.SATISFIABLE) {
			long startTime = System.nanoTime();
			Model m = solver.getModel();
			long stopTime = System.nanoTime();
			System.out.println((stopTime - startTime));
			System.out.println((stopTime - startTime) / 1000000000);
			
			/* Debug */
			if (debug) { 
				System.out.println(solver.toString());
				
				/* d1 and d2 */	
				for (int q1 = 0; q1 < numStates; q1++) {
					for (int move : alphabetMap.values())  { 
						Character input = revAlphabetMap.get(move);
						Expr state = ctx.mkInt(q1);
						Expr a = ctx.mkInt(move); 
						
						/* get state to */
						Expr d2exp = d2.apply(state, a);
						int q2 = ((IntNum) m.evaluate(d2exp, false)).getInt();
						
						/* output_len */
						Expr outputLenExpr = out_len.apply(state, a);
						int outputLen = ((IntNum) m.evaluate(outputLenExpr, false)).getInt();
						
						/* get output */
						StringBuilder outputStr = new StringBuilder("");
						for (int i = 0; i < outputLen; i++) {
							Expr<IntSort> index = ctx.mkInt(i);
							Expr d1exp = d1.apply(state, a, index);
							int outMove = ((IntNum) m.evaluate(d1exp, false)).getInt();
							Character output = revAlphabetMap.get(outMove);
							outputStr.append(output);
						}
						
						/* print d1, d2 combined for convenience */
						System.out.println("d(" + q1 + ", " + input + ", " + outputStr + ", " + q2 + ")");
					}
				}
					
				/* for which is x(q_R, q, q_T) set to TRUE? */
				for (int i = 0; i < numStates; i++) {
					for (Integer sourceState : source.getStates()) {
						for (Integer targetState : target.getStates()) {
							Expr<IntSort> sourceInt = ctx.mkInt(sourceState);
							Expr<IntSort> stateInt = ctx.mkInt(i);
							Expr<IntSort> targetInt = ctx.mkInt(targetState);
								
							Expr exp1 = x.apply(sourceInt, stateInt, targetInt);
							if (m.evaluate(exp1, false).isTrue()) {
								System.out.println("x(" + sourceState + ", " + stateInt + ", " + targetState + ")");
							}
						}
					}
				}
					
				/* for which values is e_k(i, j, q) set to TRUE? */
				exampleCount = 0;
				for (Pair<String, String> example : ioExamples) {
					int inputLen = example.first.length();
					int outputLen = example.second.length();
					System.out.println(example.first);
					System.out.println(example.second);
						
					FuncDecl e = eFuncs[exampleCount];
							
					for (int i = 0; i <= inputLen; i++) {
						for (int j = 0; j <= outputLen; j++) {
							for (int q = 0; q < numStates; q++) {
								Expr<IntSort> stateInt = ctx.mkInt(q);
								Expr exp1 = e.apply(ctx.mkInt(i), ctx.mkInt(j), stateInt);
								if (m.evaluate(exp1, false).isTrue()) {
									String inputStr = example.first.substring(0, i);
									String outputStr = example.second.substring(0, j);
									System.out.println("e_" + exampleCount + "(" + inputStr + ", " + outputStr + ", " + stateInt + ")");
								}
							}
						}
					}
					exampleCount++;
				}
		    }
			
			/* Add transitions to FT */
			for (int q1 = 0; q1 < numStates; q1++) {
				for (int move : alphabetMap.values())  { 
					Character input = revAlphabetMap.get(move);
					Expr state = ctx.mkInt(q1);
					Expr a = ctx.mkInt(move); 
					
					/* get state to */
					Expr d2exp = d2.apply(state, a);
					int q2 = ((IntNum) m.evaluate(d2exp, false)).getInt();
					
					/* output_len */
					Expr outputLenExpr = out_len.apply(state, a);
					int outputLen = ((IntNum) m.evaluate(outputLenExpr, false)).getInt();
					
					/* get output */
					List<CharFunc> outputFunc = new ArrayList<CharFunc>();
					for (int i = 0; i < outputLen; i++) {
						Expr<IntSort> index = ctx.mkInt(i);
						Expr d1exp = d1.apply(state, a, index);
						int outMove = ((IntNum) m.evaluate(d1exp, false)).getInt();
						Character output = revAlphabetMap.get(outMove);
						outputFunc.add(new CharConstant(output));
					}
					
					transitionsFT.add(new SFTInputMove<CharPred, CharFunc, Character>(q1, q2, new CharPred(input), outputFunc));
				}
			}
					
		}
		

		HashMap<Integer, Set<List<Character>>> finStates = new HashMap<Integer, Set<List<Character>>>();
		SFT<CharPred, CharFunc, Character> mySFT = SFT.MkSFT(transitionsFT, 0, finStates, ba);
		
		return mySFT;
		
	}
		
}



