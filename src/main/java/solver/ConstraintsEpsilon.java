package solver;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;

import automata.sfa.SFA;
import automata.sfa.SFAMove;
import theory.BooleanAlgebra;
import theory.characters.CharPred;
import utilities.Pair;

public class ConstraintsEpsilon {
	
	/**
	 * Builds constraints: functions d, f and x
	 * @param ctx
	 * @param solver
	 * @param alphabet
	 * @param source
	 * @param target
	 * @param numStates
	 * @param ioExamples
	 * @param ba
	 * @return
	 * @throws TimeoutException
	 */
	@SuppressWarnings("unchecked")
	public static Solver mkConstraints(Context ctx, Solver solver, HashMap<Character, Integer> alphabet, 
			SFA<CharPred, Character> source, SFA<CharPred, Character> target, int numStates, 
			List<Pair<String, String>> ioExamples, BooleanAlgebra<CharPred, Character> ba) throws TimeoutException {
		
		/* int and bool sorts */
		Sort I = ctx.getIntSort();
		Sort B = ctx.getBoolSort();
		
		/* declare d : Q x \Sigma' x \Sigma' x Q-> {1, 0} */
		Sort[] argsToD = new Sort[]{ I, I, I, I };
		FuncDecl<Sort> d = ctx.mkFuncDecl("d", argsToD, B);
		
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < numStates; j++) {
				for (int k = 0; k < numStates; k++) {
					for (int a = 0; a < alphabet.size(); a++) {
						for (int b = 0; b < alphabet.size(); b++) {
							
							/* if j & k are the same state */ 
							if (j == k) continue;
							
							/* standard case to ensure determinism */
							Expr<IntSort>[] args1 = new Expr[4];
							args1[0] = ctx.mkInt(i);
							args1[1] = ctx.mkInt(a);
							args1[2] = ctx.mkInt(b);
							args1[3] = ctx.mkInt(j);
							
							Expr res1 = d.apply(args1);
							BoolExpr c1 = ctx.mkNot(res1);
							
							Expr<IntSort>[] args2 = new Expr[4];
							args2[0] = ctx.mkInt(i);
							args2[1] = ctx.mkInt(a);
							args2[2] = ctx.mkInt(b);
							args2[3] = ctx.mkInt(k);
							
							Expr res2 = d.apply(args2);
							BoolExpr c2 = ctx.mkNot(res2);
							
							BoolExpr c3 = ctx.mkOr(c1, c2);
							solver.add(c3);
						}
					}
				}
			}
		}
		
		/* no epsilon-epsilon moves */
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < numStates; j++) {
				int epsilon = alphabet.size() - 1;
				Expr<IntSort>[] args = new Expr[4];
				args[0] = ctx.mkInt(i);
				args[1] = ctx.mkInt(epsilon);
				args[2] = ctx.mkInt(epsilon);
				args[3] = ctx.mkInt(j);
					
				Expr res = d.apply(args);
				BoolExpr c1 = ctx.mkNot(res);
				solver.add(c1);
			}
		}
		
		/* totality */
		for (int i = 0; i < numStates; i++) {
			for (int a = 0; a < alphabet.size(); a++) {
				Expr term = ctx.mkFalse();
				for (int b = 0; b < alphabet.size(); b++) {
					for (int j = 0; j < numStates; j++) {
						Expr<IntSort>[] args1 = new Expr[4];
						args1[0] = ctx.mkInt(i);
						args1[1] = ctx.mkInt(a);
						args1[2] = ctx.mkInt(b);
						args1[3] = ctx.mkInt(j);
						
						Expr res = d.apply(args1);
						term = ctx.mkOr(term, res);
					}
				}
				solver.add(term);
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
		
		Collection<SFAMove<CharPred, Character>> sourceTransitions = source.getTransitions();
		Collection <SFAMove<CharPred, Character>> targetTransitions = target.getTransitions();
		
		/* x function constraints */
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < numStates; j++) {
				for (SFAMove<CharPred, Character> sTransition : sourceTransitions) {
					for (SFAMove<CharPred, Character> tTransition : targetTransitions) {
						Expr<IntSort> sourceFrom = ctx.mkInt(sTransition.from);
						Expr<IntSort> sourceTo = ctx.mkInt(sTransition.to);
						Character sourceChar = sTransition.getWitness(ba);
						Expr<IntSort> sourceCharInt = ctx.mkInt(alphabet.get(sourceChar));
						
						Expr<IntSort> targetFrom = ctx.mkInt(tTransition.from);
						Expr<IntSort> targetTo = ctx.mkInt(tTransition.to);
						Character targetChar = tTransition.getWitness(ba);
						Expr<IntSort> targetCharInt = ctx.mkInt(alphabet.getOrDefault(targetChar, alphabet.size())); /* ad-hoc */
						
						Expr<IntSort> stateFrom = ctx.mkInt(i);
						Expr<IntSort> stateTo = ctx.mkInt(j);
						
						Expr exp1 = x.apply(sourceFrom, stateFrom, targetFrom);
						Expr exp2 = d.apply(stateFrom, sourceCharInt, targetCharInt, stateTo);
						Expr exp3 = x.apply(sourceTo, stateTo, targetTo);
						
						BoolExpr antecedent = ctx.mkAnd(exp1, exp2);
						BoolExpr c = ctx.mkImplies(antecedent, exp3);
						solver.add(c);
						
						Expr epsilon = ctx.mkInt(alphabet.size() - 1);
						/* epsilon in input */
						exp2 = d.apply(stateFrom, epsilon, targetCharInt, stateTo);
						exp3 = x.apply(sourceFrom, stateTo, targetTo);
						antecedent = ctx.mkAnd(exp1, exp2);
						c = ctx.mkImplies(antecedent, exp3);
						solver.add(c);
						
						/* epsilon in output */
						exp2 = d.apply(stateFrom, sourceCharInt, epsilon, stateTo);
						exp3 = x.apply(sourceTo, stateTo, targetFrom);
						antecedent = ctx.mkAnd(exp1, exp2);
						c = ctx.mkImplies(antecedent, exp3);
						solver.add(c);
					}
				}
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
			for (Integer sourceState : source.getFinalStates()) {
				for (Integer targetState : target.getFinalStates()) {
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
		
		/* debug */
		System.out.println(solver.toString());
		if (solver.check() == Status.SATISFIABLE) {
			Model m = solver.getModel();
			System.out.println(m.getFuncInterp(x));
			
			for (int q1 = 0; q1 < numStates; q1++) {
				for (int q2 = 0; q2 < numStates; q2++) {
					for (int a = 0; a < alphabet.size(); a++) {
						for (int b = 0; b < alphabet.size(); b++) {
							Expr<IntSort>[] args1 = new Expr[4];
							args1[0] = ctx.mkInt(q1);
							args1[1] = ctx.mkInt(a);
							args1[2] = ctx.mkInt(b);
							args1[3] = ctx.mkInt(q2);
							Expr exp = d.apply(args1);
							if (m.evaluate(exp, false).isTrue()) {
								System.out.println(q1 + ", " + a + ", " + b + ", " + q2);
							}
						}	
					}
				}
			}
			
		}
		
		
		/* constraints for each example string */
		int k = 0;
		for (Pair<String, String> example : ioExamples) {
			String inputString = example.first;
			String outputString = example.second;
			
			/* declare s_i : N x N x Q -> {0, 1} */
			Sort[] argsToS = new Sort[]{ I, I, I };
			String funcName = "s_" + Integer.toString(k);
			FuncDecl<Sort> s = ctx.mkFuncDecl(funcName, argsToS, B);
			
			/* 0-th index */
			if (!inputString.isEmpty() && !outputString.isEmpty()) {
				Expr<IntSort> zero = ctx.mkInt(0);
				Expr c = s.apply(zero, zero, zero);
				solver.add(c);
			}
			
			/* incrementing */
			for (int q1 = 0; q1 < numStates; q1++) {
				for (int q2 = 0; q2 < numStates; q2++) {
					for (int i = 0; i < inputString.length() - 1; i++) {
						for (int j = 0; j < outputString.length() - 1; j++) {
							Expr<IntSort> inputPosition = ctx.mkInt(i);
							Expr<IntSort> outputPosition = ctx.mkInt(j);
							Expr<IntSort> nextInputPosition = ctx.mkInt(i + 1);
							Expr<IntSort> nextOutputPosition = ctx.mkInt(j + 1);
							Expr<IntSort> stateFrom = ctx.mkInt(q1);
							Expr<IntSort> stateTo = ctx.mkInt(q2);
							
							/* character at i-th position of inputString */
							Character ith = inputString.charAt(i);
							Expr<IntSort> ithInput = ctx.mkInt(alphabet.get(ith));
							
							/* character at j-th position of outputString */
							Character jth = outputString.charAt(j);
							Expr<IntSort> jthOutput = ctx.mkInt(alphabet.get(jth));
							
							Expr sexp = s.apply(inputPosition, outputPosition, stateFrom);
							Expr dexp = d.apply(stateFrom, ithInput, jthOutput, stateTo);
							Expr antecedent = ctx.mkAnd(sexp, dexp);
							Expr consequent = s.apply(nextInputPosition, nextOutputPosition, stateTo);
							Expr c = ctx.mkImplies(antecedent, consequent);
							solver.add(c);
						}
					}
				}
			}
			
			/* length of strings --> final state */
			for (int q = 0; q < numStates; q++) {
				Expr<IntSort> inputStrLength = ctx.mkInt(inputString.length());
				Expr<IntSort> outputStrLength = ctx.mkInt(outputString.length());
				Expr<IntSort> state = ctx.mkInt(q);
				
				/*
				 * Expr antecedent = s.apply(inputStrLength, outputStrLength, state); Expr
				 * consequent = f.apply(state); Expr c = ctx.mkImplies(antecedent, consequent);
				 * solver.add(c);
				 */
			}
			
			/* counter */
			k++;
		}
		
		return solver;
	}
	
	/* TODO: write function and change return type */
	public static void mkTransducer(Model m, int numStates) {
		for (int q1 = 0; q1 < numStates; q1++) {
			
		}
		
	}
	
	
}
