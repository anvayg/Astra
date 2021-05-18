package solver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BitVecNum;
import com.microsoft.z3.BitVecSort;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;

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

public class ConstraintsBV {

	/* Fields/instance variables */
	Context ctx;
	SFA<CharPred, Character> source; 
	SFA<CharPred, Character> target; 
	Set<Character> alphabet;
	HashMap<Character, Integer> alphabetMap;
	BooleanAlgebraSubst<CharPred, CharFunc, Character> ba;
		
	/* Constructor */
	public ConstraintsBV(Context ctx, SFA<CharPred, Character> source, SFA<CharPred, Character> target, HashMap<Character, 
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
	
	
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public static SFT<CharPred, CharFunc, Character> mkConstraints(Context ctx, Solver solver, HashMap<Character, Integer> alphabetMap, 
			SFA<CharPred, Character> source, SFA<CharPred, Character> target, int numStates, int length, int[] fraction, 
			List<Pair<String, String>> ioExamples, SFA<CharPred, Character> template, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba, 
			boolean debug) throws TimeoutException {
		/* bit-vec and bool sorts */
		BitVecSort BV = ctx.mkBitVecSort(8);
		Sort B = ctx.getBoolSort();
		
		/* some useful constants */
		BitVecExpr numStatesInt = (BitVecNum) ctx.mkNumeral(numStates, BV);
		BitVecExpr alphabetSize = (BitVecNum) ctx.mkNumeral(alphabetMap.size(), BV);
		BitVecExpr zero = (BitVecNum) ctx.mkNumeral(0, BV);
		BitVecExpr bound = (BitVecNum) ctx.mkNumeral(length, BV);
		
		/* declare d_1:  */
		Sort[] argsToD1 = new Sort[]{ BV, BV, BV };
		FuncDecl<BitVecSort> d1 = ctx.mkFuncDecl("d1", argsToD1, BV);
		
		/* declare out_len */
		Sort[] argsToOutLen = new Sort[]{ BV, BV };
		FuncDecl<BitVecSort> out_len = ctx.mkFuncDecl("out_len", argsToOutLen, BV);
		
		/* declare d_2 : Q x \Sigma -> Q */
		Sort[] argsToD2 = new Sort[]{ BV, BV };
		FuncDecl<BitVecSort> d2 = ctx.mkFuncDecl("d2", argsToD2, BV);
		
		/* restrict range of d_1, d_2 and out_len */
		for (int i = 0; i < numStates; i++) {	// q 
			BitVecExpr q = (BitVecNum) ctx.mkNumeral(i, BV);
			
			for (int move : alphabetMap.values())  {
				BitVecExpr a = (BitVecNum) ctx.mkNumeral(move, BV);
				
				/* 0 <= out_len(q, a) <= l */
				Expr outLenExpr = out_len.apply(q, a);
				solver.add(ctx.mkBVSLE(zero, outLenExpr));
				solver.add(ctx.mkBVSLE(outLenExpr, bound));
				
				/* make variable q' = d2(q, a) */
				Expr qPrime = d2.apply(q, a);
				
				/* 0 <= qPrime < numStates; range only needs to be encoded once */
				solver.add(ctx.mkBVSLE(zero, qPrime));
				solver.add(ctx.mkBVSLT(qPrime, numStatesInt));
				
				for (int l = 0; l < length; l++) {
					BitVecExpr index = (BitVecNum) ctx.mkNumeral(l, BV);
					Expr d1exp = d1.apply(q, a, index);
					
					/* 0 <= d1(q, a, index) < alphabetSize */
					solver.add(ctx.mkBVSLE(zero, d1exp));
					solver.add(ctx.mkBVSLT(d1exp, alphabetSize)); 
				}
			}
		}
		
		/* declare x : Q_R x Q x Q_T -> {1, 0} */
		Sort[] argsToX = new Sort[]{ BV, BV, BV };
		FuncDecl<Sort> x = ctx.mkFuncDecl("x", argsToX, B);
		
		/* initial states: x(q^0_R, q^0, q^0_T) */
		BitVecExpr sourceInit = (BitVecNum) ctx.mkNumeral(source.getInitialState(), BV);
		BitVecExpr targetInit = (BitVecNum) ctx.mkNumeral(target.getInitialState(), BV);
		Expr res = x.apply(sourceInit, zero, targetInit);
		solver.add(res);
		
		/* d_R: transition relation of source */
		Sort[] argsToDR = new Sort[]{ BV, BV };
		FuncDecl<BitVecSort> dR = ctx.mkFuncDecl("dR", argsToDR, BV);
		
		/* encode d_R */
		Collection<SFAMove<CharPred, Character>> sourceTransitions = source.getTransitions();
		for (SFAMove<CharPred, Character> transition : sourceTransitions) {
			Integer stateFrom = transition.from;
			BitVecExpr q1 = (BitVecNum) ctx.mkNumeral(stateFrom, BV);
			
			Character move = transition.getWitness(ba); // there should only be 1
			BitVecExpr a = (BitVecNum) ctx.mkNumeral(alphabetMap.get(move), BV);
			
			Integer stateTo = transition.to;
			BitVecExpr q2 = (BitVecNum) ctx.mkNumeral(stateTo, BV);
			
			Expr dexp = dR.apply(q1, a);
			solver.add(ctx.mkEq(dexp, q2));
		}
		
		/* d_T: transition relation of target */
		Sort[] argsToDT = new Sort[]{ BV, BV };
		FuncDecl<BitVecSort> dT = ctx.mkFuncDecl("dT", argsToDT, BV);
		
		/* encode d_T */
		Collection<SFAMove<CharPred, Character>> targetTransitions = target.getTransitions();
		for (SFAMove<CharPred, Character> transition : targetTransitions) {
			Integer stateFrom = transition.from;
			BitVecExpr q1 = (BitVecNum) ctx.mkNumeral(stateFrom, BV);
			
			Character move = transition.getWitness(ba); // there should only be 1
			BitVecExpr a = (BitVecNum) ctx.mkNumeral(alphabetMap.get(move), BV);
			
			Integer stateTo = transition.to;
			BitVecExpr q2 = (BitVecNum) ctx.mkNumeral(stateTo, BV);
			
			Expr dexp = dT.apply(q1, a);
			solver.add(ctx.mkEq(dexp, q2));
		}
		
		/* declare f_R : Q -> {0, 1} */
		FuncDecl<Sort> f_R = ctx.mkFuncDecl("f_R", BV, B);
		for (Integer sourceState : source.getStates()) {
			BitVecExpr stateInt = (BitVecNum) ctx.mkNumeral(sourceState, BV);
			Expr c = f_R.apply(stateInt);
			if (!source.isFinalState(sourceState)) c = ctx.mkNot(c);
			solver.add(c);
		}
		
		/* declare f_T : Q -> {0, 1} */
		FuncDecl<Sort> f_T = ctx.mkFuncDecl("f_T", BV, B);
		for (Integer targetState : target.getStates()) {
			BitVecExpr stateInt = (BitVecNum) ctx.mkNumeral(targetState, BV);
			Expr c = f_T.apply(stateInt);
			if (!target.isFinalState(targetState)) c = ctx.mkNot(c);
			solver.add(c);
		}
		
		/* declare edit-dist: Q x \Sigma -> Z */
		Sort[] argsToEd = new Sort[]{ BV, BV };
		FuncDecl<BitVecSort> edDist = ctx.mkFuncDecl("ed_dist", argsToEd, BV);
		
		/* declare C: Q_R x Q x Q_T -> Z */
		Sort[] argsToC = new Sort[]{ BV, BV, BV };
		FuncDecl<BitVecSort> energy = ctx.mkFuncDecl("C", argsToC, BV);
		
		/* C(q^0_R, q^0, q^0_T) = 0 */
		solver.add(ctx.mkEq(energy.apply(zero, zero, zero), zero));
		
		
		/* edit-distance constraints */
		for (int i = 0; i < numStates; i++) {	// q 
			BitVecExpr q = (BitVecNum) ctx.mkNumeral(i, BV);
				
			for (SFAMove<CharPred, Character> sourceTransition : sourceTransitions) {
				Integer stateFrom = sourceTransition.from;
				Character move = sourceTransition.getWitness(ba);
				BitVecExpr qR = (BitVecNum) ctx.mkNumeral(stateFrom, BV);
				BitVecExpr a = (BitVecNum) ctx.mkNumeral(alphabetMap.get(move), BV);
				
				/* make variable out_len(q, a) */
				Expr outLenExpr = out_len.apply(q, a);
				
				/* make variable ed_dist(q, a) */
				Expr edDistExpr = edDist.apply(q, a);
				
				/* c_0 = d1(q, a, 0), c_1 = d1(q, a, 1), ..., c_{l-1} = d1(q, a, l-1) */
				
				/* make array of output chars */
				Expr[] outputChars = new Expr[length];
				
				/* comparing a to each output char */
				Expr disjunct = ctx.mkFalse();
				
				for (int l = 0; l < length; l++) {
					BitVecExpr index = (BitVecNum) ctx.mkNumeral(l, BV);
					Expr d1exp = d1.apply(q, a, index);
					outputChars[l] = d1exp;
					Expr lt = ctx.mkBVSLT(index, outLenExpr);
					Expr eq = ctx.mkEq(a, d1exp);
					disjunct = ctx.mkOr(disjunct, ctx.mkAnd(lt, eq));
				}

				/* for condition where the output chars don't include 'a' */
				Expr negDisjunct = ctx.mkNot(disjunct);
				
				/* (k = 0) ==> ed_dist(q, a) = 1 */
				Expr lenEq = ctx.mkEq(outLenExpr, zero);
				Expr edDistEqOne = ctx.mkEq(edDistExpr, ctx.mkNumeral(1, BV));
				Expr impl1 = ctx.mkImplies(lenEq, edDistEqOne);
				
				/* \neg (k = 0) ==> ed_dist(q, a) = k - 1 */
				Expr lenNotZero = ctx.mkNot(lenEq);
				Expr edDistKMinus1 = ctx.mkEq(edDistExpr, ctx.mkBVSub(outLenExpr, ctx.mkNumeral(1, BV))); 	
				Expr impl2 = ctx.mkImplies(lenNotZero, edDistKMinus1);
				
				/* \neg (k = 0) ==> ed_dist(q, a) = k */
				Expr edDistK = ctx.mkEq(edDistExpr, outLenExpr); 
				Expr impl3 = ctx.mkImplies(lenNotZero, edDistK);
				
				/* ed_dist constraint 1 */
				Expr consequent = ctx.mkAnd(impl1, impl2);
				solver.add(ctx.mkImplies(disjunct, consequent));
					
				/* ed_dist constraint 2 */
				consequent = ctx.mkAnd(impl1, impl3);
				solver.add(ctx.mkImplies(negDisjunct, consequent));
			}
		}
		
		for (int i = 0; i < numStates; i++) {	// q 
			BitVecExpr q = (BitVecNum) ctx.mkNumeral(i, BV);
				
			for (SFAMove<CharPred, Character> sourceTransition : sourceTransitions) {
				Integer stateFrom = sourceTransition.from;
				Character move = sourceTransition.getWitness(ba);
				BitVecExpr qR = (BitVecNum) ctx.mkNumeral(stateFrom, BV);
				BitVecExpr a = (BitVecNum) ctx.mkNumeral(alphabetMap.get(move), BV);
				
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
					BitVecExpr index = (BitVecNum) ctx.mkNumeral(l, BV);
					Expr d1exp = d1.apply(q, a, index);
					outputChars[l] = d1exp; 
				}
				
				/* ed_dist(q, a) */
				Expr edDistExpr = edDist.apply(q, a);
				
				/* m - (n x ed_dist(q, a)) */
				BitVecExpr m = (BitVecNum) ctx.mkNumeral(fraction[0], BV); 
				BitVecExpr n = (BitVecNum) ctx.mkNumeral(fraction[1], BV);
				BitVecExpr diff = ctx.mkBVSub(m, ctx.mkBVMul(n, edDistExpr));
				
				for (Integer targetFrom : target.getStates()) {
					BitVecExpr qT = (BitVecNum) ctx.mkNumeral(targetFrom, BV);
					
					
					/* q1 = dT(qT, c0), q2 = dT(q1, c1), ..., q_l = dT(q_{l-1}, c_{l-1}) */
					
					/* make array of destination states in target */
					Expr[] dstStates = new Expr[length];
					
					dstStates[0] = dT.apply(qT, outputChars[0]);
					for (int l = 1; l < length; l++) { 		// start from 1 in the loop
						dstStates[l] = dT.apply(dstStates[l - 1], outputChars[l]); // changed to l from l-1
					}
					
					
					/* x(q_R, q, q_T) */
					Expr xExpr = x.apply(qR, q, qT);
		
					/* C(q_R, q, q_T) */
					Expr cExpr = energy.apply(qR, q, qT);
					
					/* expressions for implications: out_len(q, a) = 0 ==> 
					 * x(qR', q', qT) /\ C(q_R, q, q_T) >= C(qRPrime, qPrime, qT) - diff */
					
					/* special case for 0 */
					Expr lenEq = ctx.mkEq(outLenExpr, zero);
					Expr xExprPrime = x.apply(qRPrime, qPrime, qT);
					
					/* C(q_R, q, q_T) >= C(qRPrime, qPrime, qT) - diff */
					Expr cExprPrime = energy.apply(qRPrime, qPrime, qT);
					Expr cGreaterExpr = ctx.mkBVSGE(cExpr, ctx.mkBVSub(cExprPrime, diff));
					
					Expr c = ctx.mkImplies(lenEq, ctx.mkAnd(xExprPrime, cGreaterExpr));
					
					
					/* loop for the rest */
					Expr consequent = c;
					for (int l = 0; l < length; l++) {
						int outputLength = l + 1;
						lenEq = ctx.mkEq(outLenExpr, ctx.mkInt(outputLength));
						xExprPrime = x.apply(qRPrime, qPrime, dstStates[l]);
						
						cExprPrime = energy.apply(qRPrime, qPrime, dstStates[l]);
						cGreaterExpr = ctx.mkBVSGE(cExpr, ctx.mkBVSub(cExprPrime, diff));
						
						c = ctx.mkImplies(lenEq, ctx.mkAnd(xExprPrime, cGreaterExpr));
						consequent = ctx.mkAnd(consequent, c);
					}
					
					/* make big constraint */
					solver.add(ctx.mkImplies(xExpr, consequent));
				}
			}
		}
		
		/* x(q_R, q, q_T) /\ f_R(q_R) -> f_T(q_T) /\ (C(q_R, q, q_T) >= 0) */
		for (int i = 0; i < numStates; i++) {
			for (Integer sourceState : source.getStates()) {
				for (Integer targetState : target.getStates()) {
					BitVecExpr sourceInt = (BitVecNum) ctx.mkNumeral(sourceState, BV);
					BitVecExpr stateInt = (BitVecNum) ctx.mkNumeral(i, BV);
					BitVecExpr targetInt = (BitVecNum) ctx.mkNumeral(targetState, BV);
					
					Expr xExpr = x.apply(sourceInt, stateInt, targetInt);
					Expr fRExp = f_R.apply(sourceInt);
					Expr antecedent = ctx.mkAnd(xExpr, fRExp);
					
					Expr cExpr = energy.apply(sourceInt, stateInt, targetInt);
					Expr cGreaterExp = ctx.mkBVSGE(cExpr, zero);
					Expr fTExp = f_T.apply(targetInt);
					Expr consequent = ctx.mkAnd(fTExp, cGreaterExp);
					
					Expr c = ctx.mkImplies(antecedent, consequent);
					solver.add(c);
				}
			}
		}
		
		
		
		/* Reconstruct transducer */
		HashMap<Integer, Character> revAlphabetMap = reverseMap(alphabetMap);
		Set<SFTMove<CharPred, CharFunc, Character>> transitionsFT = new HashSet<SFTMove<CharPred, CharFunc, Character>>();
		
		long startTime = System.nanoTime();
		if (solver.check() == Status.SATISFIABLE) {
			Model m = solver.getModel();
			long stopTime = System.nanoTime();
			System.out.println((stopTime - startTime));
			System.out.println((stopTime - startTime) / 1000000000);
			
			/* Debug */
			if (debug) { 
				System.out.println(solver.toString());
				
				/* d1 and d2 */	
				for (int q1 = 0; q1 < numStates; q1++) {
					BitVecExpr state = (BitVecNum) ctx.mkNumeral(q1, BV);
					
					for (int move : alphabetMap.values())  { 
						Character input = revAlphabetMap.get(move);
						BitVecExpr a = (BitVecNum) ctx.mkNumeral(move, BV); 
						
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
						
						/* edit-distance of transitions */
						Expr edDistExpr = edDist.apply(state, a);
						int editDist = ((IntNum) m.evaluate(edDistExpr, false)).getInt();
						System.out.println("edit-distance(" + q1 + ", " + input + ", " + outputStr + ") = " + editDist);
					}
				}
					
				/* values for which x(q_R, q, q_T) is set to TRUE and corresponding values of C(q_R, q, q_T) */
				for (int i = 0; i < numStates; i++) {
					for (Integer sourceState : source.getStates()) {
						for (Integer targetState : target.getStates()) {
							BitVecExpr sourceInt = (BitVecNum) ctx.mkNumeral(sourceState, BV);
							BitVecNum stateInt = (BitVecNum) ctx.mkNumeral(i, BV);
							BitVecExpr targetInt = (BitVecNum) ctx.mkNumeral(targetState, BV);
								
							Expr exp1 = x.apply(sourceInt, stateInt, targetInt);
							Expr exp2 = energy.apply(sourceInt, stateInt, targetInt);
							if (m.evaluate(exp1, false).isTrue()) {
								System.out.println("x(" + sourceState + ", " + stateInt.getInt() + ", " + targetState + ")");
								int energyVal = ((IntNum) m.evaluate(exp2, false)).getInt();
								System.out.println("C(" + sourceState + ", " + stateInt.getInt() + ", " + targetState + ")" + " = " + energyVal);
							}
							
							
						}
					}
				}
		    }
			
			/* Add transitions to FT */
			for (int q1 = 0; q1 < numStates; q1++) {
				for (int move : alphabetMap.values())  { 
					Character input = revAlphabetMap.get(move);
					BitVecExpr state = (BitVecNum) ctx.mkNumeral(q1, BV);
					BitVecExpr a = (BitVecNum) ctx.mkNumeral(move, BV); 
						
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
									
					SFTInputMove<CharPred, CharFunc, Character> newTrans = new SFTInputMove<CharPred, CharFunc, Character>(q1, q2, new CharPred(input), outputFunc);
					transitionsFT.add(newTrans);
				}
			}
					
		} else {
			long stopTime = System.nanoTime();
			System.out.println((stopTime - startTime));
			System.out.println((stopTime - startTime) / 1000000000);
		}
		
		HashMap<Integer, Set<List<Character>>> finStates = new HashMap<Integer, Set<List<Character>>>();
		SFT<CharPred, CharFunc, Character> mySFT = SFT.MkSFT(transitionsFT, 0, finStates, ba);
		
		return mySFT;
	}
}

