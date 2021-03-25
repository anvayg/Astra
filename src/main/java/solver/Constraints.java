package solver;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;

import automata.sfa.SFA;
import automata.sfa.SFAMove;
import theory.BooleanAlgebraSubst;
import theory.characters.CharFunc;
import theory.characters.CharPred;
import transducers.sft.SFT;
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
		
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public static void mkConstraints(Context ctx, Solver solver, HashMap<Character, Integer> alphabetMap, 
			SFA<CharPred, Character> source, SFA<CharPred, Character> target, int numStates, 
			List<Pair<String, String>> ioExamples, BooleanAlgebraSubst<CharPred, CharFunc, Character> ba, 
			int length, boolean debug) throws TimeoutException {
		
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
		FuncDecl<Sort> dT = ctx.mkFuncDecl("dR", argsToDT, I);
		
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
				Integer stateFrom = sourceTransition.to;
				Character move = sourceTransition.getWitness(ba);
				Expr<IntSort> qR = ctx.mkInt(stateFrom);
				Expr<IntSort> a = ctx.mkInt(alphabetMap.get(move));

				for (Integer targetFrom : target.getStates()) {
					Expr<IntSort> qT = ctx.mkInt(targetFrom);
						
					/* 0 <= out_len(q, a) <= l */
					Expr outLenExpr = out_len.apply(q, a);
					solver.add(ctx.mkLe(zero, outLenExpr));
					solver.add(ctx.mkLe(outLenExpr, bound));
						
					/* make variable q_R' = d_R(q_R, a), the equality is already encoded */
					Expr qRPrime = dR.apply(qR, a);
					
					
					/* make variable q' = d2(q, a) */
					Expr qPrime = d2.apply(q, a);
					
					/* 0 <= qPrime < numStates */
					solver.add(ctx.mkLe(zero, qPrime));
					solver.add(ctx.mkLt(qPrime, numStatesInt));
								
					
					/* c_0 = d1(q, a, 0), c_1 = d1(q, a, 1), ..., c_{l-1} = d1(q, a, l-1) */
					
					/* make array of output chars */
					Expr[] outputChars = new Expr[length];
					
					for (int l = 0; l < length; l++) {
						Expr<IntSort> index = ctx.mkInt(l);
						outputChars[l] = d1.apply(q, a, index);
					}
					
					
					/* q1 = dT(qT, c0), q2 = dT(q1, c1), ..., q_l = dT(q_{l-1}, c_{l-1}) */
					
					/* make array of destination states in target */
					Expr[] dstStates = new Expr[length];
					
					dstStates[0] = dT.apply(qT, outputChars[0]);
					for (int l = 1; l < length; l++) { 		// start from 1 in the loop
						Expr<IntSort> index = ctx.mkInt(l);
						dstStates[l] = dT.apply(dstStates[l - 1], outputChars[l - 1]);
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
		
		
		
	}
		
}



