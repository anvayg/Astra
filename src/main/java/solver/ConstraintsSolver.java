package solver;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.tuple.ImmutablePair;
import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BitVecNum;
import com.microsoft.z3.BitVecSort;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.TupleSort;

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

public class ConstraintsSolver {
	/* Fields/instance variables */
	Context ctx;
	Solver solver;
	SFA<CharPred, Character> source; 
	SFA<CharPred, Character> target;
	int numStates;
	int numLookaheadStates;
	int outputBound;
	String distanceType;
	int[] distance;
	List<Pair<String, String>> ioExamples;
	SFA<CharPred, Character> template;
	SFT<CharPred, CharFunc, Character> solution;
	Set<Character> alphabet;
	HashMap<Character, Integer> alphabetMap;
	BooleanAlgebraSubst<CharPred, CharFunc, Character> ba;
	
	/* Sorts and FuncDecls */
	BitVecSort BV;
	Sort B;
	
	BitVecExpr numStatesInt;
	BitVecExpr numLookaheadStatesInt;
	BitVecExpr alphabetSize;
	BitVecExpr zero;
	BitVecExpr bound;
	
	FuncDecl<BitVecSort> d1;
	FuncDecl<BitVecSort> d2;
	FuncDecl<BitVecSort> out_len;
	FuncDecl<Sort> x;
	FuncDecl<BitVecSort> dR;
	FuncDecl<BitVecSort> dT;
	FuncDecl<Sort> f_R;
	FuncDecl<Sort> f_T;
	FuncDecl<BitVecSort> edDist;
	FuncDecl<BitVecSort> energy;
	
	/* BV Pair Datatype */
	TupleSort pair;
	FuncDecl first;	// projections
	FuncDecl second;
	FuncDecl[] eFuncs;
	
	FuncDecl<BitVecSort> dL;
	
	Map<CharPred, Pair<CharPred, ArrayList<Integer>>> idToMinterms;
	
	
	/* Constructor */
	public ConstraintsSolver(Context ctx, SFA<CharPred, Character> source, SFA<CharPred, Character> target, 
			HashMap<Character, Integer> alphabetMap, int numStates, int outputBound, List<Pair<String, String>> ioExamples, 
			String distanceType, int[] distance, SFA<CharPred, Character> template, 
			SFT<CharPred, CharFunc, Character> solution, Map<CharPred, Pair<CharPred, ArrayList<Integer>>> minterms, 
			BooleanAlgebraSubst<CharPred, CharFunc, Character> ba) {
		this.ctx = ctx;
		this.solver = ctx.mkSolver();
		this.source = source;
		this.target = target;
		this.alphabet = alphabetMap.keySet();
		this.numStates = numStates;
		this.outputBound = outputBound;
		this.ioExamples = ioExamples;
		this.distanceType = distanceType;
		this.distance = distance;
		this.template = template;
		this.solution = solution;
		this.alphabetMap = alphabetMap;
		this.idToMinterms = minterms;
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
	public void encodeTypes() throws TimeoutException {
		
		/* initial states: x(q^0_R, q^0, q^0_T) */
		BitVecExpr sourceInit = (BitVecNum) ctx.mkNumeral(source.getInitialState(), BV);
		BitVecExpr targetInit = (BitVecNum) ctx.mkNumeral(target.getInitialState(), BV);
		Expr res = x.apply(sourceInit, zero, targetInit);
		solver.add(res);
		
		Collection<SFAMove<CharPred, Character>> sourceTransitions = source.getTransitions();
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
				Expr[] outputChars = new Expr[outputBound];
				
				for (int l = 0; l < outputBound; l++) {
					BitVecExpr index = (BitVecNum) ctx.mkNumeral(l, BV);
					Expr d1exp = d1.apply(q, a, index);
					outputChars[l] = d1exp; 
				}
				
				for (Integer targetFrom : target.getStates()) {
					BitVecExpr qT = (BitVecNum) ctx.mkNumeral(targetFrom, BV);
					
					
					/* q1 = dT(qT, c0), q2 = dT(q1, c1), ..., q_l = dT(q_{l-1}, c_{l-1}) */
					
					/* make array of destination states in target */
					Expr[] dstStates = new Expr[outputBound];
					
					dstStates[0] = dT.apply(qT, outputChars[0]);
					for (int l = 1; l < outputBound; l++) { 		// start from 1 in the loop
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
					for (int l = 0; l < outputBound; l++) {
						int outputLength = l + 1;
						lenEq = ctx.mkEq(outLenExpr, (BitVecNum) ctx.mkNumeral(outputLength, BV));
						xExprPrime = x.apply(qRPrime, qPrime, dstStates[l]);
						
						c = ctx.mkImplies(lenEq, xExprPrime);
						consequent = ctx.mkAnd(consequent, c);
					}
					
					/* make big constraint */
					solver.add(ctx.mkImplies(xExpr, consequent));
				}
			}
		}
		
		/* x(q_R, q, q_T) /\ f_R(q_R) -> f_T(q_T) */
		for (int i = 0; i < numStates; i++) {
			for (Integer sourceState : source.getStates()) {
				for (Integer targetState : target.getStates()) {
					BitVecExpr sourceInt = (BitVecNum) ctx.mkNumeral(sourceState, BV);
					BitVecExpr stateInt = (BitVecNum) ctx.mkNumeral(i, BV);
					BitVecExpr targetInt = (BitVecNum) ctx.mkNumeral(targetState, BV);
					
					Expr xExpr = x.apply(sourceInt, stateInt, targetInt);
					Expr fRExp = f_R.apply(sourceInt);
					Expr antecedent = ctx.mkAnd(xExpr, fRExp);
					
					Expr fTExp = f_T.apply(targetInt);
					Expr consequent = fTExp;
					
					Expr c = ctx.mkImplies(antecedent, consequent);
					solver.add(c);
				}
			}
		}
	}
	
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public void encodeDistanceBounded() throws TimeoutException {
		/* In this case, the fraction must be a whole number (it should have denominator 1) */
		int numEdits = distance[0];
		BitVecExpr editsBound = (BitVecNum) ctx.mkNumeral(numEdits, BV);
		
		/* C(q^0_R, q^0, q^0_T) = numEdits */
		solver.add(ctx.mkEq(energy.apply(zero, zero, zero), editsBound));
		
		Collection<SFAMove<CharPred, Character>> sourceTransitions = source.getTransitions();
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
				Expr[] outputChars = new Expr[outputBound];
				
				for (int l = 0; l < outputBound; l++) {
					BitVecExpr index = (BitVecNum) ctx.mkNumeral(l, BV);
					Expr d1exp = d1.apply(q, a, index);
					outputChars[l] = d1exp; 
				}
				
				/* ed_dist(q, a) */
				Expr edDistExpr = edDist.apply(q, a);
				
				/* m - (n x ed_dist(q, a)) */
				BitVecExpr m = (BitVecNum) ctx.mkNumeral(distance[0], BV); 
				BitVecExpr n = (BitVecNum) ctx.mkNumeral(distance[1], BV);
				BitVecExpr diff = ctx.mkBVSub(m, ctx.mkBVMul(n, edDistExpr));
				
				for (Integer targetFrom : target.getStates()) {
					BitVecExpr qT = (BitVecNum) ctx.mkNumeral(targetFrom, BV);
					
					
					/* q1 = dT(qT, c0), q2 = dT(q1, c1), ..., q_l = dT(q_{l-1}, c_{l-1}) */
					
					/* make array of destination states in target */
					Expr[] dstStates = new Expr[outputBound];
					
					dstStates[0] = dT.apply(qT, outputChars[0]);
					for (int l = 1; l < outputBound; l++) { 		// start from 1 in the loop
						dstStates[l] = dT.apply(dstStates[l - 1], outputChars[l]); // changed to l from l-1
					}
		
					/* C(q_R, q, q_T) */
					Expr cExpr = energy.apply(qR, q, qT);
					
					/* special case for 0 */
					Expr lenEq = ctx.mkEq(outLenExpr, zero);
					
					/* C(qRPrime, qPrime, qT) = C(q_R, q, q_T) - ed_dist(q, a) */
					Expr cExprPrime = energy.apply(qRPrime, qPrime, qT);
					Expr cNewExpr = ctx.mkEq(cExprPrime, ctx.mkBVSub(cExpr, edDistExpr));
					
					Expr c = ctx.mkImplies(lenEq, cNewExpr);
					solver.add(c);
					
					
					/* loop for the rest */
					for (int l = 0; l < outputBound; l++) {
						int outputLength = l + 1;
						lenEq = ctx.mkEq(outLenExpr, (BitVecNum) ctx.mkNumeral(outputLength, BV));
						
						cExprPrime = energy.apply(qRPrime, qPrime, dstStates[l]);
						cNewExpr = ctx.mkEq(cExprPrime, ctx.mkBVSub(cExpr, edDistExpr));
						
						c = ctx.mkImplies(lenEq, cNewExpr);
						solver.add(c);
					}
				}
			}
		}
		
		/* C(q_R, q, q_T) >= 0 */
		for (int i = 0; i < numStates; i++) {
			for (Integer sourceState : source.getStates()) {
				for (Integer targetState : target.getStates()) {
					BitVecExpr sourceInt = (BitVecNum) ctx.mkNumeral(sourceState, BV);
					BitVecExpr stateInt = (BitVecNum) ctx.mkNumeral(i, BV);
					BitVecExpr targetInt = (BitVecNum) ctx.mkNumeral(targetState, BV);
										
					Expr cExpr = energy.apply(sourceInt, stateInt, targetInt);
					Expr cGreaterExp = ctx.mkBVSGE(cExpr, zero);
					solver.add(cGreaterExp);
				}
			}
		}
	}
	
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public void encodeDistanceMean() throws TimeoutException {
		
		/* C(q^0_R, q^0, q^0_T) = 0 */
		solver.add(ctx.mkEq(energy.apply(zero, zero, zero), zero));
		
		Collection<SFAMove<CharPred, Character>> sourceTransitions = source.getTransitions();
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
				Expr[] outputChars = new Expr[outputBound];
				
				for (int l = 0; l < outputBound; l++) {
					BitVecExpr index = (BitVecNum) ctx.mkNumeral(l, BV);
					Expr d1exp = d1.apply(q, a, index);
					outputChars[l] = d1exp; 
				}
				
				/* ed_dist(q, a) */
				Expr edDistExpr = edDist.apply(q, a);
				
				/* m - (n x ed_dist(q, a)) */
				BitVecExpr m = (BitVecNum) ctx.mkNumeral(distance[0], BV); 
				BitVecExpr n = (BitVecNum) ctx.mkNumeral(distance[1], BV);
				BitVecExpr diff = ctx.mkBVSub(m, ctx.mkBVMul(n, edDistExpr));
				
				for (Integer targetFrom : target.getStates()) {
					BitVecExpr qT = (BitVecNum) ctx.mkNumeral(targetFrom, BV);
					
					
					/* q1 = dT(qT, c0), q2 = dT(q1, c1), ..., q_l = dT(q_{l-1}, c_{l-1}) */
					
					/* make array of destination states in target */
					Expr[] dstStates = new Expr[outputBound];
					
					dstStates[0] = dT.apply(qT, outputChars[0]);
					for (int l = 1; l < outputBound; l++) { 		// start from 1 in the loop
						dstStates[l] = dT.apply(dstStates[l - 1], outputChars[l]); // changed to l from l-1
					}
		
					/* C(q_R, q, q_T) */
					Expr cExpr = energy.apply(qR, q, qT);
					
					/* expressions for implications: out_len(q, a) = 0 ==> 
					 * C(q_R, q, q_T) >= C(qRPrime, qPrime, qT) - diff */
					
					/* special case for 0 */
					Expr lenEq = ctx.mkEq(outLenExpr, zero);
					
					/* C(q_R, q, q_T) >= C(qRPrime, qPrime, qT) - diff */
					Expr cExprPrime = energy.apply(qRPrime, qPrime, qT);
					Expr cGreaterExpr = ctx.mkBVSGE(cExpr, ctx.mkBVSub(cExprPrime, diff));
					
					Expr c = ctx.mkImplies(lenEq, cGreaterExpr);
					solver.add(c);
					
					
					/* loop for the rest */
					for (int l = 0; l < outputBound; l++) {
						int outputLength = l + 1;
						lenEq = ctx.mkEq(outLenExpr, (BitVecNum) ctx.mkNumeral(outputLength, BV));
						
						cExprPrime = energy.apply(qRPrime, qPrime, dstStates[l]);
						cGreaterExpr = ctx.mkBVSGE(cExpr, ctx.mkBVSub(cExprPrime, diff));
						
						c = ctx.mkImplies(lenEq, cGreaterExpr);
						solver.add(c);
					}
					
				}
			}
		}
		
		/* x(q_R, q, q_T) /\ f_R(q_R) -> (C(q_R, q, q_T) >= 0) */
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
					Expr consequent = cGreaterExp;
					
					Expr c = ctx.mkImplies(antecedent, consequent);
					solver.add(c);
				}
			}
		}
	}
	
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public void encodeDistancePreferential() throws TimeoutException {
		
	}
	
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public void encodeDistance() throws TimeoutException {
		/* edit-distance constraints of individual transitions */
		Collection<SFAMove<CharPred, Character>> sourceTransitions = source.getTransitions();
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
				Expr[] outputChars = new Expr[outputBound];
				
				/* comparing a to each output char */
				Expr disjunct = ctx.mkFalse();
				
				for (int l = 0; l < outputBound; l++) {
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
		
		/* Different kinds of distances */
		if (distanceType.equals("bounded")) encodeDistanceBounded();
		
		else if (distanceType.equals("mean")) encodeDistanceMean();
		
		else if (distanceType.equals("preferential")) encodeDistancePreferential();
		
		else throw new IllegalArgumentException("Unsupported distanceType");
	}
	
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public void encodeExamples() throws TimeoutException {
		/* example constraints */
		eFuncs = new FuncDecl[ioExamples.size()];
		Collection<SFAMove<CharPred, Character>> sourceTransitions = source.getTransitions();
		
		int exampleCount = 0;
		for (Pair<String, String> ioExample : ioExamples) {
			/* verify example */
			if (SFAOperations.getStateInFA(source, source.getInitialState(), ioExample.first, ba) == -1) throw new IllegalArgumentException("Illegal example for source: " + ioExample.first);
			if (SFAOperations.getStateInFA(target, target.getInitialState(), ioExample.second, ba) == -1) throw new IllegalArgumentException("Illegal example for target: " + ioExample.second);
			
			int[] inputArr = stringToIntArray(alphabetMap, ioExample.first);
			int[] outputArr = stringToIntArray(alphabetMap, ioExample.second);
			
			/* declare function e_k: k x input_position -> (output_position, Q) */
			Sort[] args = new Sort[] {BV};
			eFuncs[exampleCount] = ctx.mkFuncDecl("e " + String.valueOf(exampleCount), args, pair);
			FuncDecl e = eFuncs[exampleCount];
			
			/* initial position : e_k(0) = (0, q_0) */
			Expr initPair = pair.mkDecl().apply(zero, zero);
			solver.add(ctx.mkEq(e.apply(zero), initPair));
			
			int inputLen = ioExample.first.length();
			BitVecExpr inputLength = (BitVecNum) ctx.mkNumeral(inputLen, BV);
			int outputLen = ioExample.second.length();
			BitVecExpr outputLength = (BitVecNum) ctx.mkNumeral(outputLen, BV);
			
			/* 0 <= e_k(l1).first <= outputLen and 0 <= e_k(l1).second < numStates */
			for (int l = 0; l <= inputLen; l++) {
					Expr eExpr = e.apply((BitVecNum) ctx.mkNumeral(l, BV));
					Expr eExprFirst = first.apply(eExpr);
					Expr eExprSecond = second.apply(eExpr);
					
					/* restrict values of first */
					solver.add(ctx.mkBVSLE(zero, eExprFirst));
					solver.add(ctx.mkBVSLE(eExprFirst, outputLength));
					
					/* restrict values of second */
					solver.add(ctx.mkBVSLE(zero, eExprSecond));
					solver.add(ctx.mkBVSLT(eExprSecond, numStatesInt));
			}
			
			/* final position : e_k(l1).first = l2 */
			Expr eExprFirst = first.apply(e.apply(inputLength));
			solver.add(ctx.mkEq(eExprFirst, outputLength));
			
			for (int s = 0; s < numStates; s++) {	// q 
				BitVecExpr q = (BitVecNum) ctx.mkNumeral(s, BV);
					
				for (SFAMove<CharPred, Character> sourceTransition : sourceTransitions) {
					Integer stateFrom = sourceTransition.from;
					Character move = sourceTransition.getWitness(ba);
					BitVecExpr qR = (BitVecNum) ctx.mkNumeral(stateFrom, BV);
					BitVecExpr a = (BitVecNum) ctx.mkNumeral(alphabetMap.get(move), BV);
					
					/* out_len(q, a) */
					Expr outLenExpr = out_len.apply(q, a);
						
					/* make variable q_R' = d_R(q_R, a), the equality is already encoded */
					// Expr qRPrime = dR.apply(qR, a);
					
					
					/* make variable q' = d2(q, a) */
					Expr qPrime = d2.apply(q, a);
								
					
					/* c_0 = d1(q, a, 0), c_1 = d1(q, a, 1), ..., c_{l-1} = d1(q, a, l-1) */
					
					/* make array of output chars */
					Expr[] outputChars = new Expr[outputBound];
					
					for (int l = 0; l < outputBound; l++) {
						BitVecExpr index = (BitVecNum) ctx.mkNumeral(l, BV);
						Expr d1exp = d1.apply(q, a, index);
						outputChars[l] = d1exp;
					}
					
					
					for (Integer targetFrom : target.getStates()) {
						BitVecExpr qT = (BitVecNum) ctx.mkNumeral(targetFrom, BV);
						
						/* q1 = dT(qT, c0), q2 = dT(q1, c1), ..., q_l = dT(q_{l-1}, c_{l-1}) */
						
						/* make array of destination states in target */
						Expr[] dstStates = new Expr[outputBound];
						
						dstStates[0] = dT.apply(qT, outputChars[0]);
						for (int l = 1; l < outputBound; l++) { 		// start from 1 in the loop
							dstStates[l] = dT.apply(dstStates[l - 1], outputChars[l]);
						}
						
						
						for (int i = 0; i < inputLen; i++) { 	// rationale: always read an input character, it's fine to have transition that reads last input char, 
							for (int j = 0; j <= outputLen; j++) {	// but output is already completely generated
								BitVecExpr inputPosition = (BitVecNum) ctx.mkNumeral(i, BV);
								BitVecExpr outputPosition = (BitVecNum) ctx.mkNumeral(j, BV);
								
								/* input[i+1] = a */
								BitVecExpr nextInputPosition = (BitVecNum) ctx.mkNumeral(inputArr[i], BV);
								Expr inputEq = ctx.mkEq(nextInputPosition, a);
								
								/* output needs be <= outputLen - j */
								int possibleOutputLen = Math.min(outputLen - j, outputBound);
								BitVecExpr possibleOutputLength = (BitVecNum) ctx.mkNumeral(possibleOutputLen, BV);
								
								Expr outputLe = ctx.mkBVSLE(outLenExpr, possibleOutputLength);
								
								/* e_k(i) = (j, q) */
								Expr eExpr = ctx.mkEq(e.apply(inputPosition), pair.mkDecl().apply(outputPosition, q));
								
								/* expressions for implications: out_len(q, a) = 0 ==> e_k(i+1) = (j, q') */
								
								/* special case for 0 */
								Expr lenEq = ctx.mkEq(outLenExpr, zero);
								Expr eExprPrime = ctx.mkEq(e.apply((BitVecNum) ctx.mkNumeral(i + 1, BV)), pair.mkDecl().apply(outputPosition, qPrime));
								
								Expr c = ctx.mkImplies(lenEq, eExprPrime);
								
								/* loop for the rest */
								Expr consequent = ctx.mkAnd(outputLe, c);
								for (int l = 0; l < possibleOutputLen; l++) { 
									int outputGenLength = l + 1;
									lenEq = ctx.mkEq(outLenExpr, (BitVecNum) ctx.mkNumeral(outputGenLength, BV));
									eExprPrime = ctx.mkEq(e.apply((BitVecNum) ctx.mkNumeral(i + 1, BV)), 
											pair.mkDecl().apply((BitVecNum) ctx.mkNumeral(j + outputGenLength, BV), qPrime));
									
									/* equalities */
									Expr stringEqualities = ctx.mkTrue();
									for (int inc = 1; inc <= outputGenLength; inc++) {
										int index = (j + inc) - 1;
										BitVecExpr nextPosition = (BitVecNum) ctx.mkNumeral(outputArr[index], BV);
										Expr eq = ctx.mkEq(nextPosition, outputChars[inc - 1]);
										stringEqualities = ctx.mkAnd(stringEqualities, eq);
									}
									
									c = ctx.mkImplies(lenEq, ctx.mkAnd(stringEqualities, eExprPrime)); 
									consequent = ctx.mkAnd(consequent, c);
								}
								
								
								/* make big constraint */
								Expr antecedent = ctx.mkAnd(eExpr, inputEq);
								solver.add(ctx.mkImplies(antecedent, consequent));
							}
						}
						
					}
					
				}
			}
			
			exampleCount++;
		}
	}
	
	
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public Pair<SFT<CharPred, CharFunc, Character>, Long> mkConstraints(String smtFile, boolean debug) throws TimeoutException {
		/* Set params */
		Params p = ctx.mkParams();
		p.add("smt.relevancy", 0);
		p.add("smt.bv.eq_axioms", false);
		p.add("smt.phase_caching_on", 80000);
		solver.setParameters(p);
		
		/* Ensures numStates is correct */
		if (template != null) {
			this.numStates = template.stateCount();
		}
		
		/* bit-vec and bool sorts */
		BV = ctx.mkBitVecSort(8);
		B = ctx.getBoolSort();
		
		/* some useful constants */
		numStatesInt = (BitVecNum) ctx.mkNumeral(numStates, BV);
		alphabetSize = (BitVecNum) ctx.mkNumeral(alphabetMap.size(), BV);
		zero = (BitVecNum) ctx.mkNumeral(0, BV);
		bound = (BitVecNum) ctx.mkNumeral(outputBound, BV);
		
		/* d_R: transition relation of source */
		Sort[] argsToDR = new Sort[]{ BV, BV };
		dR = ctx.mkFuncDecl("dR", argsToDR, BV);
		
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
		dT = ctx.mkFuncDecl("dT", argsToDT, BV);
		
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
		f_R = ctx.mkFuncDecl("f_R", BV, B);
		for (Integer sourceState : source.getStates()) {
			BitVecExpr stateInt = (BitVecNum) ctx.mkNumeral(sourceState, BV);
			Expr c = f_R.apply(stateInt);
			if (!source.isFinalState(sourceState)) c = ctx.mkNot(c);
			solver.add(c);
		}
		
		/* declare f_T : Q -> {0, 1} */
		f_T = ctx.mkFuncDecl("f_T", BV, B);
		for (Integer targetState : target.getStates()) {
			BitVecExpr stateInt = (BitVecNum) ctx.mkNumeral(targetState, BV);
			Expr c = f_T.apply(stateInt);
			if (!target.isFinalState(targetState)) c = ctx.mkNot(c);
			solver.add(c);
		}
		
		/* declare d_1:  */
		Sort[] argsToD1 = new Sort[]{ BV, BV, BV };
		d1 = ctx.mkFuncDecl("d1", argsToD1, BV);
		
		/* declare out_len */
		Sort[] argsToOutLen = new Sort[]{ BV, BV };
		out_len = ctx.mkFuncDecl("out_len", argsToOutLen, BV);
		
		/* declare d_2 : Q x \Sigma -> Q */
		Sort[] argsToD2 = new Sort[]{ BV, BV };
		d2 = ctx.mkFuncDecl("d2", argsToD2, BV);
		
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
				
				for (int l = 0; l < outputBound; l++) {
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
		x = ctx.mkFuncDecl("x", argsToX, B);
		
		/* declare edit-dist: Q x \Sigma -> Z */
		Sort[] argsToEd = new Sort[]{ BV, BV };
		edDist = ctx.mkFuncDecl("ed_dist", argsToEd, BV);
		
		/* declare C: Q_R x Q x Q_T -> Z */
		Sort[] argsToC = new Sort[]{ BV, BV, BV };
		energy = ctx.mkFuncDecl("C", argsToC, BV);
		
		
		this.pair = ctx.mkTupleSort(ctx.mkSymbol("mkPair"), // name of tuple constructor
				new Symbol[] { ctx.mkSymbol("first"), ctx.mkSymbol("second") }, // names of projection operators
				new Sort[] { BV, BV } // types of projection operators
			);
		this.first = pair.getFieldDecls()[0];	// projections
		this.second = pair.getFieldDecls()[1];
		

		/* Input-Output Types Constraints */
		encodeTypes();
		
	
		/* Input-Output Distance Constraints */
		encodeDistance();
		
		
		/* Input-Output Example Constraints */
		encodeExamples();
		
		
		/* Put constraints on 'incompatible' minterms */
		if (idToMinterms != null) {
			/* Process alphabet */
			Set<Character> singleChars = new HashSet<Character>();
			Set<Character> multipleChars = new HashSet<Character>();
			
			for (Character a : alphabet) {
				CharPred minterm = SFAOperations.findSatisfyingMinterm(a, idToMinterms);
				if (minterm.intervals.size() == 1) {
					ImmutablePair<Character, Character> interval = minterm.intervals.get(0);
					if (interval.right - interval.left == 0) {
						singleChars.add(a);
					} else {
						multipleChars.add(a);
					}
				} else {
					multipleChars.add(a);
				}
			}
			
			/* Single-char minterm cannot output multiple-char minterm */
			for (int i = 0; i < numStates; i++) {	// q 
				BitVecExpr q = (BitVecNum) ctx.mkNumeral(i, BV);
				
				for (Character move : singleChars)  {
					BitVecExpr a = (BitVecNum) ctx.mkNumeral(alphabetMap.get(move), BV);

					for (int l = 0; l < outputBound; l++) {
						BitVecExpr index = (BitVecNum) ctx.mkNumeral(l, BV);
						Expr d1exp = d1.apply(q, a, index);

						for (Character out : multipleChars) {
							BitVecExpr b = (BitVecNum) ctx.mkNumeral(alphabetMap.get(out), BV);
							solver.add(ctx.mkNot(ctx.mkEq(d1exp, b)));
						}
					}
				}
			}
			
		}
		
		
		/* Use the d2 relation (the successor states) of the template, if one is provided, and enforce it */
		if (template != null) {
			for (SFAMove<CharPred, Character> transition : template.getTransitions()) { 	
				Integer stateFrom = transition.from;
				Character move = transition.getWitness(ba);
				Integer stateTo = transition.to;
				
				BitVecExpr q = (BitVecNum) ctx.mkNumeral(stateFrom, BV);
				BitVecExpr a = (BitVecNum) ctx.mkNumeral(alphabetMap.get(move), BV);
				BitVecExpr qPrime = (BitVecNum) ctx.mkNumeral(stateTo, BV);
				
				solver.add(ctx.mkEq(d2.apply(q, a), qPrime));
			}
		}
		
		/* If previous solution provided, construct satisfying assignment and negate it */
		if (solution != null) {
			Expr negModel = ctx.mkTrue();
			Collection<Integer> states = solution.getStates();
			for (SFTInputMove<CharPred, CharFunc, Character> transition : solution.getInputMovesFrom(states)) {
				Integer stateFrom = transition.from;
				Character move = transition.getWitness(ba);
				Integer stateTo = transition.to;
				List<CharFunc> outputFunc = transition.outputFunctions;
				
				BitVecExpr q = (BitVecNum) ctx.mkNumeral(stateFrom, BV);
				BitVecExpr a = (BitVecNum) ctx.mkNumeral(alphabetMap.get(move), BV);
				BitVecExpr qPrime = (BitVecNum) ctx.mkNumeral(stateTo, BV);
				BitVecExpr outputLen = (BitVecNum) ctx.mkNumeral(outputFunc.size(), BV);
				
				/* d2exp */
				Expr d2exp = d2.apply(q, a);
				negModel = ctx.mkAnd(negModel, ctx.mkEq(d2exp, qPrime));
				
				/* outputLenExpr */
				Expr outputLenExpr = out_len.apply(q, a);
				negModel = ctx.mkAnd(negModel, ctx.mkEq(outputLenExpr, outputLen));
				
				/* d1exp: iterate through outputFunc */
				int index = 0;
				for (CharFunc f : outputFunc) {
					if (f != null && f instanceof CharConstant) { 	// all the CharFuncs should be constants
						Character out = ((CharConstant)f).c;
						BitVecExpr outMoveNum = (BitVecNum) ctx.mkNumeral(alphabetMap.get(out), BV);
						
						Expr d1exp = d1.apply(q, a, (BitVecNum) ctx.mkNumeral(index, BV));
						negModel = ctx.mkAnd(negModel, ctx.mkEq(d1exp, outMoveNum));
					}
				}
				
			}
			
			/* negate model */
			solver.add(ctx.mkNot(negModel));
		}
		
		
		/* Print SMT string to smtFile */
		try {
			if (smtFile != null) {
				BufferedWriter br = new BufferedWriter(new FileWriter(new File(smtFile)));
				br.write(solver.toString());
				br.write("(check-sat)");
				br.close();
			}
		} catch (IOException e1) {
			e1.printStackTrace();
		}
		
		return constructSFT(debug);
	}
	
	
	public Pair<SFT<CharPred, CharFunc, Character>, Long> constructSFT(boolean debug) throws TimeoutException {
		/* Reconstruct transducer */
		HashMap<Integer, Character> revAlphabetMap = reverseMap(alphabetMap);
		Set<SFTMove<CharPred, CharFunc, Character>> transitionsFT = new HashSet<SFTMove<CharPred, CharFunc, Character>>();
		
		long startTime = System.nanoTime();
		long stopTime = 0; 	// gets set later
		if (solver.check() == Status.SATISFIABLE) {
			Model m = solver.getModel();
			stopTime = System.nanoTime();
			System.out.println((stopTime - startTime));
			System.out.println((stopTime - startTime) / 1000000000);
			
			/* Debug */
			if (debug) {
				
				/* d1 and d2 */	
				for (int q1 = 0; q1 < numStates; q1++) {
					BitVecExpr state = (BitVecNum) ctx.mkNumeral(q1, BV);
					
					for (int move : alphabetMap.values())  { 
						Character input = revAlphabetMap.get(move);
						BitVecExpr a = (BitVecNum) ctx.mkNumeral(move, BV); 
						
						/* get state to */
						Expr d2exp = d2.apply(state, a);
						int q2 = ((BitVecNum) m.evaluate(d2exp, false)).getInt();
						
						/* output_len */
						Expr outputLenExpr = out_len.apply(state, a);
						int outputLen = ((BitVecNum) m.evaluate(outputLenExpr, false)).getInt();
						
						/* get output */
						StringBuilder outputStr = new StringBuilder("");
						for (int i = 0; i < outputLen; i++) {
							BitVecExpr index = (BitVecNum) ctx.mkNumeral(i, BV);
							Expr d1exp = d1.apply(state, a, index);
							int outMove = ((BitVecNum) m.evaluate(d1exp, false)).getInt();
							Character output = revAlphabetMap.get(outMove);
							outputStr.append(output);
						}
						
						/* print d1, d2 combined for convenience */
						System.out.println("d(" + q1 + ", " + input + ", " + outputStr + ", " + q2 + ")");
						
						/* edit-distance of transitions */
						Expr edDistExpr = edDist.apply(state, a);
						int editDist = ((BitVecNum) m.evaluate(edDistExpr, false)).getInt();
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
								int energyVal = ((BitVecNum) m.evaluate(exp2, false)).getInt();
								System.out.println("C(" + sourceState + ", " + stateInt.getInt() + ", " + targetState + ")" + " = " + energyVal);
							}
							
						}
					}
				}
				
				/* values of e(i) */
		    }
			
			/* Add transitions to FT */
			if (template != null) {
				/* Only add 'relevant' transitions */
				for (SFAMove<CharPred, Character> transition : template.getTransitions()) { 	
					Integer stateFrom = transition.from;
					Character move = transition.getWitness(ba);
					Integer stateTo = transition.to;
					
					BitVecExpr q1 = (BitVecNum) ctx.mkNumeral(stateFrom, BV);
					BitVecExpr a = (BitVecNum) ctx.mkNumeral(alphabetMap.get(move), BV);
					
					/* output_len */
					Expr outputLenExpr = out_len.apply(q1, a);
					BitVecNum outputLenNum = (BitVecNum) m.evaluate(outputLenExpr, false);
					int outputLen = outputLenNum.getInt();
								
					/* get output */
					List<CharFunc> outputFunc = new ArrayList<CharFunc>();
					for (int i = 0; i < outputLen; i++) {
						BitVecExpr index = (BitVecNum) ctx.mkNumeral(i, BV);
						Expr d1exp = d1.apply(q1, a, index);
						BitVecNum outMoveNum = (BitVecNum) m.evaluate(d1exp, false);
						int outMove = outMoveNum.getInt();
						Character output = revAlphabetMap.get(outMove);
						outputFunc.add(new CharConstant(output));
					}
								
					SFTInputMove<CharPred, CharFunc, Character> newTrans = new SFTInputMove<CharPred, CharFunc, Character>(stateFrom, stateTo, new CharPred(move), outputFunc);
					transitionsFT.add(newTrans);
				}
				
			} else {
				for (int q1 = 0; q1 < numStates; q1++) {
					for (int move : alphabetMap.values())  { 
						Character input = revAlphabetMap.get(move);
						BitVecExpr state = (BitVecNum) ctx.mkNumeral(q1, BV);
						BitVecExpr a = (BitVecNum) ctx.mkNumeral(move, BV); 
							
						/* get state to */
						Expr d2exp = d2.apply(state, a);
						BitVecNum q2num = (BitVecNum) m.evaluate(d2exp, false);
						int q2 = q2num.getInt();
										
						/* output_len */
						Expr outputLenExpr = out_len.apply(state, a);
						BitVecNum outputLenNum = (BitVecNum) m.evaluate(outputLenExpr, false);
						int outputLen = outputLenNum.getInt();
										
						/* get output */
						List<CharFunc> outputFunc = new ArrayList<CharFunc>();
						for (int i = 0; i < outputLen; i++) {
							BitVecExpr index = (BitVecNum) ctx.mkNumeral(i, BV);
							Expr d1exp = d1.apply(state, a, index);
							BitVecNum outMoveNum = (BitVecNum) m.evaluate(d1exp, false);
							int outMove = outMoveNum.getInt();
							Character output = revAlphabetMap.get(outMove);
							outputFunc.add(new CharConstant(output));
						}
										
						SFTInputMove<CharPred, CharFunc, Character> newTrans = new SFTInputMove<CharPred, CharFunc, Character>(q1, q2, new CharPred(input), outputFunc);
						transitionsFT.add(newTrans);
					}
				}
			}
			
		} else {
			stopTime = System.nanoTime();
		}
		
		HashMap<Integer, Set<List<Character>>> finStates = new HashMap<Integer, Set<List<Character>>>();
		SFT<CharPred, CharFunc, Character> mySFT = SFT.MkSFT(transitionsFT, 0, finStates, ba);
		
		return new Pair<SFT<CharPred, CharFunc, Character>, Long>(mySFT, ((stopTime - startTime) / 1000000));
	}

}
