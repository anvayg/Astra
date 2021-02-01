package z3;


import java.util.HashMap;
import com.microsoft.z3.*;

public class z3test {
	
	/**
	 * z3 test borrowed from JavaExample
	 * 
	 */
	static void logicExample(Context ctx) {
		System.out.println("LogicTest");
		
		BitVecSort bvs = ctx.mkBitVecSort(32);
        Expr x = ctx.mkConst("x", bvs);
        Expr y = ctx.mkConst("y", bvs);
        BoolExpr eq = ctx.mkEq(x, y);
        
        // Use a solver for QF_BV
        Solver s = ctx.mkSolver("QF_BV");
        s.add(eq);
        Status res = s.check();
        System.out.println("solver result: " + res);
	}
	
	public static void main(String[] args) {
		HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        
        logicExample(ctx);
	}
	
}
