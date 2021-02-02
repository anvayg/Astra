package solver;

import java.util.Collection;
import java.util.HashMap;

import org.sat4j.specs.TimeoutException;

import com.microsoft.z3.*;
import automata.sfa.*;
import theory.BooleanAlgebra;
import theory.characters.*;

public class Constraints {
	
	/**
	 * Transducer constraints: uninterpreted functions d, f and x 
	 * 
	 * @param ctx
	 * @throws TimeoutException 
	 */
	public void transducerConstraints(Context ctx, HashMap<Character, Integer> alphabet, 
			SFA<CharPred, Character> source, SFA<CharPred, Character> target, int numStates, 
			BooleanAlgebra<CharPred, Character> ba) throws TimeoutException {
		
		/* int and bool sorts */
		Sort I = ctx.getIntSort();
		Sort B = ctx.getBoolSort();
		
		Solver solver = ctx.mkSolver();
		
		/* declare d : Q x \Sigma' x \Sigma' x Q-> {1, 0} */
		Sort[] argsToD = new Sort[]{ I, I, I, I };
		FuncDecl<Sort> d = ctx.mkFuncDecl("d", argsToD, B);
		
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < numStates; j++) {
				for (int k = 0; k < numStates; k++) {
					for (int a = 0; a < alphabet.size(); a++) {
						for (int b = 0; b < alphabet.size(); b++) {
							
							/* no epsilon-epsilon moves */
							if (a == alphabet.size() - 1 && b == alphabet.size() - 1) {
								Expr<IntSort>[] args = new Expr[4];
								args[0] = ctx.mkInt(i);
								args[1] = ctx.mkInt(a);
								args[2] = ctx.mkInt(b);
								args[3] = ctx.mkInt(j);
								
								Expr res = d.apply(args);
								BoolExpr c1 = ctx.mkNot(res);
								solver.add(c1);
							}
							
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
		
		/* declare x : Q_R x Q x Q_T -> {1, 0} */
		Sort[] argsToX = new Sort[]{ I, I, I };
		FuncDecl<Sort> x = ctx.mkFuncDecl("x", argsToX, B);
		
		/* initial states */
		Expr<IntSort> sourceInit = ctx.mkInt(source.getInitialState());
		Expr<IntSort> targetInit = ctx.mkInt(target.getInitialState());
		Expr<IntSort> init = ctx.mkInt(0);
		Expr res = x.apply(sourceInit, init, targetInit);
		// BoolExpr c = ctx.mkEq(res, ctx.mkTrue()); 
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
						Expr<IntSort> targetCharInt = ctx.mkInt(alphabet.get(targetChar));
						
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
		
		
	}
	
}
