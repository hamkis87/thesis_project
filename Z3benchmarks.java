package my_z3_test;
/*++
 Copyright (c) 2012 Microsoft Corporation

Module Name:

    Program.java

Abstract:

    Z3 Java API: Example program

Author:

    Christoph Wintersteiger (cwinter) 2012-11-27

Notes:
    
--*/

import java.util.*;

import com.microsoft.z3.*;

class Z3benchmarks {
	
	public static void main (String[] args) {
		sat1();
	}
	
	public static void sat4l40() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		long startTime = System.currentTimeMillis();
		long endTime = 0;
		float msecondsElapsed = 0;
		
		String v1 = "x";
		String v2 = "y";
		String v3 = "z";
		String v4 = "w";
		
		Expr x = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr y = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		Expr z = ctx.mkConst(ctx.mkSymbol(v3), ctx.mkStringSort());
		Expr w = ctx.mkConst(ctx.mkSymbol(v4), ctx.mkStringSort());
		
		
		Expr xz = ctx.mkConcat((SeqExpr) x, (SeqExpr)z);
		Expr wy = ctx.mkConcat((SeqExpr) w, (SeqExpr)y);

		
		ReExpr A = ctx.mkToRe(ctx.mkString("A"));
		ReExpr B = ctx.mkToRe(ctx.mkString("B"));
		
		ReExpr AB_union = ctx.mkUnion(A,B);	
		ReExpr AB_union_plus = ctx.mkPlus(AB_union); 
		
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)xz, AB_union_plus);
		BoolExpr mem_const2 = ctx.mkInRe((SeqExpr)wy, AB_union_plus);
				
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)x));
		IntExpr lhs_len_const2 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)y));
		IntExpr lhs_len_const3 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)z));
		IntExpr lhs_len_const4 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)w));
		
		BoolExpr len_const1 = ctx.mkEq(lhs_len_const1, ctx.mkInt(80));
		BoolExpr len_const2 = ctx.mkGt(lhs_len_const1, ctx.mkInt(0));
		BoolExpr len_const3 = ctx.mkGt(lhs_len_const1, ctx.mkInt(0));
		BoolExpr len_const4 = ctx.mkGt(lhs_len_const1, ctx.mkInt(0));
		
		Expr lhs_eq1 = (SeqExpr) x;
		Expr rhs_eq1 = (SeqExpr) y;
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1); 
		
		// add membership constraints
		solver.add(mem_const1);
		solver.add(mem_const2);
		
		// add length constraints
		solver.add(len_const1);
		solver.add(len_const2);
		solver.add(len_const3);
		solver.add(len_const4);
		
		// add equality constraints
		solver.add(eq1);
		
		Status st = solver.check();
		
		endTime = System.currentTimeMillis();
		msecondsElapsed = endTime - startTime;
		System.out.println("Elapsed time (milliseconds) = " + msecondsElapsed);	
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}

	}
	
	
	public static void unsat12() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		long startTime = System.currentTimeMillis();
		long endTime = 0;
		float msecondsElapsed = 0;
		
		String v1 = "a";
		String v2 = "b";
		String v3 = "c";
		String v4 = "d";
		String v5 = "e";
		String v6 = "f";
		String v7 = "g";
		String v8 = "h";
		String v9 = "i";
		String v10 = "j";
		String v11 = "k";
		String v12 = "l";
		
		Expr a = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr b = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		Expr c = ctx.mkConst(ctx.mkSymbol(v3), ctx.mkStringSort());
		Expr d = ctx.mkConst(ctx.mkSymbol(v4), ctx.mkStringSort());
		Expr e = ctx.mkConst(ctx.mkSymbol(v5), ctx.mkStringSort());
		Expr f = ctx.mkConst(ctx.mkSymbol(v6), ctx.mkStringSort());
		Expr g = ctx.mkConst(ctx.mkSymbol(v7), ctx.mkStringSort());
		Expr h = ctx.mkConst(ctx.mkSymbol(v8), ctx.mkStringSort());
		Expr i = ctx.mkConst(ctx.mkSymbol(v9), ctx.mkStringSort());
		Expr j = ctx.mkConst(ctx.mkSymbol(v10), ctx.mkStringSort());
		Expr k = ctx.mkConst(ctx.mkSymbol(v11), ctx.mkStringSort());
		Expr l = ctx.mkConst(ctx.mkSymbol(v12), ctx.mkStringSort());
		
		Expr abc = ctx.mkConcat((SeqExpr) a, (SeqExpr)b, (SeqExpr)c);
		Expr de = ctx.mkConcat((SeqExpr) d, (SeqExpr)e);
		Expr fg = ctx.mkConcat((SeqExpr) f, (SeqExpr)g);
		Expr hi = ctx.mkConcat((SeqExpr) h, (SeqExpr)i);
		Expr ja = ctx.mkConcat((SeqExpr) j, (SeqExpr)a);
		Expr kbl = ctx.mkConcat((SeqExpr) k, (SeqExpr)b, (SeqExpr)l);

		
		ReExpr A = ctx.mkToRe(ctx.mkString("A"));
		ReExpr B = ctx.mkToRe(ctx.mkString("B"));
		ReExpr C = ctx.mkToRe(ctx.mkString("C"));
		ReExpr D = ctx.mkToRe(ctx.mkString("D"));
		ReExpr E = ctx.mkToRe(ctx.mkString("E"));
		
		ReExpr abc_conc = ctx.mkConcat(A,B,C);
		ReExpr abc_conc_plus = ctx.mkPlus(abc_conc);
		ReExpr ab_union = ctx.mkUnion(A,B);
		ReExpr ab_union_plus = ctx.mkPlus(ab_union);
		ReExpr ab_union_star = ctx.mkStar(ab_union);
		ReExpr abc_union = ctx.mkUnion(A,B,C);
		ReExpr abc_union_star = ctx.mkStar(abc_union);
		ReExpr ed_union = ctx.mkUnion(E,D);
		ReExpr ed_union_star = ctx.mkStar(ed_union);
		ReExpr dc_conc = ctx.mkConcat(D,C);
		ReExpr cd_conc = ctx.mkConcat(C,D);
		ReExpr cd_union_dc = ctx.mkUnion(dc_conc,cd_conc);
		ReExpr ea_conc = ctx.mkConcat(E,A);
		ReExpr ae_conc = ctx.mkConcat(A,E);
		ReExpr ea_union_ae = ctx.mkUnion(ea_conc,ae_conc);
		ReExpr ab = ctx.mkConcat(A,B);
		ReExpr ba = ctx.mkConcat(B,A);
		ReExpr ab_union_ba = ctx.mkUnion(ab,ba);
		ReExpr ee = ctx.mkConcat(E,E);
		ReExpr ee_plus = ctx.mkPlus(ee);
		ReExpr cd_union_dc_plus = ctx.mkPlus(cd_union_dc);
		
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)abc, ab_union);
		BoolExpr mem_const2 = ctx.mkInRe((SeqExpr)de, ed_union_star);
		BoolExpr mem_const3 = ctx.mkInRe((SeqExpr)fg, ab_union_ba);
		BoolExpr mem_const4 = ctx.mkInRe((SeqExpr)hi, cd_union_dc_plus);
		BoolExpr mem_const5 = ctx.mkInRe((SeqExpr)ja, ee_plus);
		BoolExpr mem_const6 = ctx.mkInRe((SeqExpr)kbl, abc_conc_plus);
				
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)a)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)b)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)c)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)d)));
		
		IntExpr lhs_len_const2 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)h)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)e)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)f)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)g)));
		
		IntExpr lhs_len_const3 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(2), ctx.mkLength((SeqExpr)i)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)j)));
		
		IntExpr lhs_len_const4 = (IntExpr) ctx.mkMul(ctx.mkInt(2), ctx.mkLength((SeqExpr)a));
		
		BoolExpr len_const1 = ctx.mkEq(lhs_len_const1, ctx.mkInt(4));
		BoolExpr len_const2 = ctx.mkGt(lhs_len_const2, ctx.mkInt(3));
		BoolExpr len_const3 = ctx.mkGe(lhs_len_const3, ctx.mkInt(3));
		BoolExpr len_const4 = ctx.mkGe(lhs_len_const3, ctx.mkInt(1));
		
		Expr lhs_eq1 = (SeqExpr) a;
		Expr rhs_eq1 = (SeqExpr) f;
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1);
		Expr lhs_eq2 = (SeqExpr) g;
		Expr rhs_eq2 = (SeqExpr) b;
		BoolExpr eq2 = ctx.mkEq(lhs_eq2, rhs_eq2);
		
		// add membership constraints
		solver.add(mem_const1);
		solver.add(mem_const2);
		solver.add(mem_const3);
		solver.add(mem_const4);
		solver.add(mem_const5);
		solver.add(mem_const6);
		// add length constraints
		solver.add(len_const1);
		solver.add(len_const2);
		solver.add(len_const3);
		solver.add(len_const4);
		
		// add equality constraints
		solver.add(eq1);
		solver.add(eq2);
		//solver.add(eq3);
		
		Status st = solver.check();
		
		endTime = System.currentTimeMillis();
		msecondsElapsed = endTime - startTime;
		System.out.println("Elapsed time (milliseconds) = " + msecondsElapsed);	
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}
		ctx.close();

	}
	
	
	public static void unsat10() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		long startTime = System.currentTimeMillis();
		long endTime = 0;
		float msecondsElapsed = 0;
		
		String v1 = "a";
		String v2 = "b";
		String v3 = "c";
		String v4 = "d";
		String v5 = "e";
		String v6 = "f";
		String v7 = "g";
		String v8 = "h";
		String v9 = "i";
		String v10 = "j";
		
		Expr a = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr b = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		Expr c = ctx.mkConst(ctx.mkSymbol(v3), ctx.mkStringSort());
		Expr d = ctx.mkConst(ctx.mkSymbol(v4), ctx.mkStringSort());
		Expr e = ctx.mkConst(ctx.mkSymbol(v5), ctx.mkStringSort());
		Expr f = ctx.mkConst(ctx.mkSymbol(v6), ctx.mkStringSort());
		Expr g = ctx.mkConst(ctx.mkSymbol(v7), ctx.mkStringSort());
		Expr h = ctx.mkConst(ctx.mkSymbol(v8), ctx.mkStringSort());
		Expr i = ctx.mkConst(ctx.mkSymbol(v9), ctx.mkStringSort());
		Expr j = ctx.mkConst(ctx.mkSymbol(v10), ctx.mkStringSort());
		
		Expr abc = ctx.mkConcat((SeqExpr) a, (SeqExpr)b, (SeqExpr)c);
		Expr de = ctx.mkConcat((SeqExpr) d, (SeqExpr)e);
		Expr fg = ctx.mkConcat((SeqExpr) f, (SeqExpr)g);
		Expr hi = ctx.mkConcat((SeqExpr) h, (SeqExpr)i);

		
		ReExpr A = ctx.mkToRe(ctx.mkString("A"));
		ReExpr B = ctx.mkToRe(ctx.mkString("B"));
		ReExpr C = ctx.mkToRe(ctx.mkString("C"));
		ReExpr D = ctx.mkToRe(ctx.mkString("D"));
		ReExpr E = ctx.mkToRe(ctx.mkString("E"));
		ReExpr K = ctx.mkToRe(ctx.mkString("K"));
		
		//ReExpr ab_union = ctx.mkUnion(A,B);
		//ReExpr abc_union = ctx.mkUnion(A,B,C);
		ReExpr a_plus = ctx.mkPlus(A);
		ReExpr b_plus = ctx.mkPlus(B);
		ReExpr ed_union = ctx.mkUnion(E,D);
		ReExpr ed_union_plus = ctx.mkPlus(ed_union);
		ReExpr dc_union = ctx.mkUnion(D,C);
		ReExpr dc_union_plus = ctx.mkPlus(dc_union);
		ReExpr k_plus = ctx.mkPlus(K);
		
		
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)abc, a_plus);
		BoolExpr mem_const2 = ctx.mkInRe((SeqExpr)de, ed_union_plus);
		BoolExpr mem_const3 = ctx.mkInRe((SeqExpr)fg, b_plus);
		BoolExpr mem_const4 = ctx.mkInRe((SeqExpr)hi, dc_union_plus);
		BoolExpr mem_const5 = ctx.mkInRe((SeqExpr)j, k_plus);
				
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)a)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)b)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)c)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)d)));
		
		IntExpr lhs_len_const2 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)h)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)e)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)f)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)g)));
		
		IntExpr lhs_len_const3 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(2), ctx.mkLength((SeqExpr)i)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)j)));
		
		BoolExpr len_const1 = ctx.mkEq(lhs_len_const1, ctx.mkInt(4));
		BoolExpr len_const2 = ctx.mkGt(lhs_len_const2, ctx.mkInt(3));
		BoolExpr len_const3 = ctx.mkGe(lhs_len_const3, ctx.mkInt(3));
		
		Expr lhs_eq1 = (SeqExpr) a;
		Expr rhs_eq1 = (SeqExpr) f;
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1);
		Expr lhs_eq2 = (SeqExpr) g;
		Expr rhs_eq2 = (SeqExpr) b;
		BoolExpr eq2 = ctx.mkEq(lhs_eq2, rhs_eq2);
		Expr lhs_eq3 = (SeqExpr) h;
		Expr rhs_eq3 = (SeqExpr) c;
		BoolExpr eq3 = ctx.mkEq(lhs_eq3, rhs_eq3);
		
		// add membership constraints
		solver.add(mem_const1);
		solver.add(mem_const2);
		solver.add(mem_const3);
		solver.add(mem_const4);
		solver.add(mem_const5);
		// add length constraints
		solver.add(len_const1);
		solver.add(len_const2);
		solver.add(len_const3);
		
		// add equality constraints
		solver.add(eq1);
		solver.add(eq2);
		solver.add(eq3);
		
		Status st = solver.check();
		
		endTime = System.currentTimeMillis();
		msecondsElapsed = endTime - startTime;
		System.out.println("Elapsed time (milliseconds) = " + msecondsElapsed);	
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}
		ctx.close();

	}
	
	
	public static void unsat4() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		long startTime = System.currentTimeMillis();
		long endTime = 0;
		float msecondsElapsed = 0;
		
		String v1 = "x";
		String v2 = "y";
		String v3 = "z";
		String v4 = "w";
		
		Expr x = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr y = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		Expr z = ctx.mkConst(ctx.mkSymbol(v3), ctx.mkStringSort());
		Expr w = ctx.mkConst(ctx.mkSymbol(v4), ctx.mkStringSort());
		
		
		Expr xy = ctx.mkConcat((SeqExpr) x, (SeqExpr)y);
		Expr xz = ctx.mkConcat((SeqExpr) x, (SeqExpr)z);

		
		ReExpr A = ctx.mkToRe(ctx.mkString("A"));
		ReExpr B = ctx.mkToRe(ctx.mkString("B"));
		ReExpr one = ctx.mkToRe(ctx.mkString("1"));
		ReExpr two = ctx.mkToRe(ctx.mkString("2"));
		ReExpr three = ctx.mkToRe(ctx.mkString("3"));
		
		ReExpr AB = ctx.mkConcat(A,B);
		ReExpr onetwothree = ctx.mkUnion(one,two,three);
		ReExpr AB_onetwothree_union = ctx.mkUnion(AB,onetwothree);
		
		ReExpr AB_onetwothree_union_plus = ctx.mkPlus(AB_onetwothree_union); 
		
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)xy, AB_onetwothree_union_plus);
		BoolExpr mem_const2 = ctx.mkInRe((SeqExpr)xz, AB);
		BoolExpr mem_const3 = ctx.mkInRe((SeqExpr)w, onetwothree);
				
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)y)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)x)));
		
		BoolExpr len_const1 = ctx.mkEq(lhs_len_const1, ctx.mkInt(3));
		
		Expr lhs_eq1 = ctx.mkConcat((SeqExpr) x, (SeqExpr)z);
		Expr rhs_eq1 = ctx.mkConcat((SeqExpr) y, (SeqExpr)w);
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1); 
		
		// add membership constraints
		solver.add(mem_const1);
		solver.add(mem_const2);
		solver.add(mem_const3);
		
		// add length constraints
		solver.add(len_const1);
		
		// add equality constraints
		solver.add(eq1);
		
		Status st = solver.check();
		
		endTime = System.currentTimeMillis();
		msecondsElapsed = endTime - startTime;
		System.out.println("Elapsed time (milliseconds) = " + msecondsElapsed);	
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}

	}
	
	
	public static void unsat2() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		long startTime = System.currentTimeMillis();
		long endTime = 0;
		float msecondsElapsed = 0;
		
		String v1 = "x";
		String v2 = "y";
		
		Expr x = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr y = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		
		Expr xy = ctx.mkConcat((SeqExpr) x, (SeqExpr)y);

		
		ReExpr a = ctx.mkToRe(ctx.mkString("a"));
		ReExpr b = ctx.mkToRe(ctx.mkString("b"));
		
		ReExpr ab = ctx.mkConcat(a,b);
		
		ReExpr ab_plus = ctx.mkPlus(ab); 
		
		Expr lhs_eq1 = (SeqExpr) x;
		Expr rhs_eq1 = (SeqExpr) y;
		
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)xy, ab_plus);
		
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)y));
		IntExpr lhs_len_const2 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)x));
		
		BoolExpr len_const1 = ctx.mkLt(lhs_len_const1, ctx.mkInt(6));
		BoolExpr len_const2 = ctx.mkEq(lhs_len_const2, ctx.mkInt(3));
		
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1); 
		
		// add membership constraints
		solver.add(mem_const1);
		
		// add length constraints
		solver.add(len_const1);
		solver.add(len_const2);
		
		// add equality constraints
		solver.add(eq1);
		
		Status st = solver.check();
		
		endTime = System.currentTimeMillis();
		msecondsElapsed = endTime - startTime;
		System.out.println("Elapsed time (milliseconds) = " + msecondsElapsed);	
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}

	}
	
	
	public static void sat12() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		long startTime = System.currentTimeMillis();
		long endTime = 0;
		float msecondsElapsed = 0;
		
		String v1 = "a";
		String v2 = "b";
		String v3 = "c";
		String v4 = "d";
		String v5 = "e";
		String v6 = "f";
		String v7 = "g";
		String v8 = "h";
		String v9 = "i";
		String v10 = "j";
		String v11 = "k";
		String v12 = "l";
		
		Expr a = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr b = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		Expr c = ctx.mkConst(ctx.mkSymbol(v3), ctx.mkStringSort());
		Expr d = ctx.mkConst(ctx.mkSymbol(v4), ctx.mkStringSort());
		Expr e = ctx.mkConst(ctx.mkSymbol(v5), ctx.mkStringSort());
		Expr f = ctx.mkConst(ctx.mkSymbol(v6), ctx.mkStringSort());
		Expr g = ctx.mkConst(ctx.mkSymbol(v7), ctx.mkStringSort());
		Expr h = ctx.mkConst(ctx.mkSymbol(v8), ctx.mkStringSort());
		Expr i = ctx.mkConst(ctx.mkSymbol(v9), ctx.mkStringSort());
		Expr j = ctx.mkConst(ctx.mkSymbol(v10), ctx.mkStringSort());
		Expr k = ctx.mkConst(ctx.mkSymbol(v11), ctx.mkStringSort());
		Expr l = ctx.mkConst(ctx.mkSymbol(v12), ctx.mkStringSort());
		
		Expr abc = ctx.mkConcat((SeqExpr) a, (SeqExpr)b, (SeqExpr)c);
		Expr de = ctx.mkConcat((SeqExpr) d, (SeqExpr)e);
		Expr fg = ctx.mkConcat((SeqExpr) f, (SeqExpr)g);
		Expr hi = ctx.mkConcat((SeqExpr) h, (SeqExpr)i);
		Expr ja = ctx.mkConcat((SeqExpr) j, (SeqExpr)a);
		Expr kbl = ctx.mkConcat((SeqExpr) k, (SeqExpr)b, (SeqExpr)l);

		
		ReExpr A = ctx.mkToRe(ctx.mkString("A"));
		ReExpr B = ctx.mkToRe(ctx.mkString("B"));
		ReExpr C = ctx.mkToRe(ctx.mkString("C"));
		ReExpr D = ctx.mkToRe(ctx.mkString("D"));
		ReExpr E = ctx.mkToRe(ctx.mkString("E"));
		
		ReExpr abc_conc = ctx.mkConcat(A,B,C);
		ReExpr abc_conc_plus = ctx.mkPlus(abc_conc);
		ReExpr ab_union = ctx.mkUnion(A,B);
		ReExpr ab_union_star = ctx.mkStar(ab_union);
		ReExpr abc_union = ctx.mkUnion(A,B,C);
		ReExpr abc_union_star = ctx.mkStar(abc_union);
		ReExpr ed_union = ctx.mkUnion(E,D);
		ReExpr ed_union_star = ctx.mkStar(ed_union);
		ReExpr dc_conc = ctx.mkConcat(D,C);
		ReExpr cd_conc = ctx.mkConcat(C,D);
		ReExpr cd_union_dc = ctx.mkUnion(dc_conc,cd_conc);
		ReExpr ea_conc = ctx.mkConcat(E,A);
		ReExpr ae_conc = ctx.mkConcat(A,E);
		ReExpr ea_union_ae = ctx.mkUnion(ea_conc,ae_conc);
		
		
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)abc, abc_union_star);
		BoolExpr mem_const2 = ctx.mkInRe((SeqExpr)de, ed_union_star);
		BoolExpr mem_const3 = ctx.mkInRe((SeqExpr)fg, ab_union_star);
		BoolExpr mem_const4 = ctx.mkInRe((SeqExpr)hi, cd_union_dc);
		BoolExpr mem_const5 = ctx.mkInRe((SeqExpr)ja, ea_union_ae);
		BoolExpr mem_const6 = ctx.mkInRe((SeqExpr)kbl, abc_conc_plus);
				
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)a)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)b)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)c)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)d)));
		
		IntExpr lhs_len_const2 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)h)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)e)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)f)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)g)));
		
		IntExpr lhs_len_const3 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(2), ctx.mkLength((SeqExpr)i)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)j)));
		
		BoolExpr len_const1 = ctx.mkEq(lhs_len_const1, ctx.mkInt(4));
		BoolExpr len_const2 = ctx.mkGt(lhs_len_const2, ctx.mkInt(3));
		BoolExpr len_const3 = ctx.mkGe(lhs_len_const3, ctx.mkInt(3));
		
		Expr lhs_eq1 = (SeqExpr) a;
		Expr rhs_eq1 = (SeqExpr) f;
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1);
		Expr lhs_eq2 = (SeqExpr) g;
		Expr rhs_eq2 = (SeqExpr) b;
		BoolExpr eq2 = ctx.mkEq(lhs_eq2, rhs_eq2);
		Expr lhs_eq3 = (SeqExpr) h;
		Expr rhs_eq3 = (SeqExpr) c;
		BoolExpr eq3 = ctx.mkEq(lhs_eq3, rhs_eq3);
		
		// add membership constraints
		solver.add(mem_const1);
		solver.add(mem_const2);
		solver.add(mem_const3);
		solver.add(mem_const4);
		solver.add(mem_const5);
		solver.add(mem_const6);
		// add length constraints
		solver.add(len_const1);
		solver.add(len_const2);
		solver.add(len_const3);
		
		// add equality constraints
		solver.add(eq1);
		solver.add(eq2);
		solver.add(eq3);
		
		Status st = solver.check();
		
		endTime = System.currentTimeMillis();
		msecondsElapsed = endTime - startTime;
		System.out.println("Elapsed time (milliseconds) = " + msecondsElapsed);	
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}
		ctx.close();

	}
	
	
	public static void sat10() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		long startTime = System.currentTimeMillis();
		long endTime = 0;
		float msecondsElapsed = 0;
		
		String v1 = "a";
		String v2 = "b";
		String v3 = "c";
		String v4 = "d";
		String v5 = "e";
		String v6 = "f";
		String v7 = "g";
		String v8 = "h";
		String v9 = "i";
		String v10 = "j";
		
		Expr a = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr b = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		Expr c = ctx.mkConst(ctx.mkSymbol(v3), ctx.mkStringSort());
		Expr d = ctx.mkConst(ctx.mkSymbol(v4), ctx.mkStringSort());
		Expr e = ctx.mkConst(ctx.mkSymbol(v5), ctx.mkStringSort());
		Expr f = ctx.mkConst(ctx.mkSymbol(v6), ctx.mkStringSort());
		Expr g = ctx.mkConst(ctx.mkSymbol(v7), ctx.mkStringSort());
		Expr h = ctx.mkConst(ctx.mkSymbol(v8), ctx.mkStringSort());
		Expr i = ctx.mkConst(ctx.mkSymbol(v9), ctx.mkStringSort());
		Expr j = ctx.mkConst(ctx.mkSymbol(v10), ctx.mkStringSort());
		
		Expr abc = ctx.mkConcat((SeqExpr) a, (SeqExpr)b, (SeqExpr)c);
		Expr de = ctx.mkConcat((SeqExpr) d, (SeqExpr)e);
		Expr fg = ctx.mkConcat((SeqExpr) f, (SeqExpr)g);
		Expr hi = ctx.mkConcat((SeqExpr) h, (SeqExpr)i);

		
		ReExpr A = ctx.mkToRe(ctx.mkString("A"));
		ReExpr B = ctx.mkToRe(ctx.mkString("B"));
		ReExpr C = ctx.mkToRe(ctx.mkString("C"));
		ReExpr D = ctx.mkToRe(ctx.mkString("D"));
		ReExpr E = ctx.mkToRe(ctx.mkString("E"));
		ReExpr K = ctx.mkToRe(ctx.mkString("K"));
		
		ReExpr ab_union = ctx.mkUnion(A,B);
		ReExpr ab_union_plus = ctx.mkPlus(ab_union);
		ReExpr abc_union = ctx.mkUnion(A,B,C);
		ReExpr abc_union_plus = ctx.mkPlus(abc_union);
		ReExpr ed_union = ctx.mkUnion(E,D);
		ReExpr ed_union_plus = ctx.mkPlus(ed_union);
		ReExpr dc_union = ctx.mkUnion(D,C);
		ReExpr dc_union_plus = ctx.mkPlus(dc_union);
		ReExpr k_plus = ctx.mkPlus(K);
		
		
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)abc, abc_union_plus);
		BoolExpr mem_const2 = ctx.mkInRe((SeqExpr)de, ed_union_plus);
		BoolExpr mem_const3 = ctx.mkInRe((SeqExpr)fg, ab_union_plus);
		BoolExpr mem_const4 = ctx.mkInRe((SeqExpr)hi, dc_union_plus);
		BoolExpr mem_const5 = ctx.mkInRe((SeqExpr)j, k_plus);
				
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)a)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)b)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)c)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)d)));
		
		IntExpr lhs_len_const2 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)h)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)e)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)f)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)g)));
		
		IntExpr lhs_len_const3 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(2), ctx.mkLength((SeqExpr)i)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)j)));
		
		BoolExpr len_const1 = ctx.mkEq(lhs_len_const1, ctx.mkInt(4));
		BoolExpr len_const2 = ctx.mkGt(lhs_len_const2, ctx.mkInt(3));
		BoolExpr len_const3 = ctx.mkGe(lhs_len_const3, ctx.mkInt(3));
		
		Expr lhs_eq1 = (SeqExpr) a;
		Expr rhs_eq1 = (SeqExpr) f;
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1);
		Expr lhs_eq2 = (SeqExpr) g;
		Expr rhs_eq2 = (SeqExpr) b;
		BoolExpr eq2 = ctx.mkEq(lhs_eq2, rhs_eq2);
		Expr lhs_eq3 = (SeqExpr) h;
		Expr rhs_eq3 = (SeqExpr) c;
		BoolExpr eq3 = ctx.mkEq(lhs_eq3, rhs_eq3);
		
		// add membership constraints
		solver.add(mem_const1);
		solver.add(mem_const2);
		solver.add(mem_const3);
		solver.add(mem_const4);
		solver.add(mem_const5);
		// add length constraints
		solver.add(len_const1);
		solver.add(len_const2);
		solver.add(len_const3);
		
		// add equality constraints
		solver.add(eq1);
		solver.add(eq2);
		solver.add(eq3);
		
		Status st = solver.check();
		
		endTime = System.currentTimeMillis();
		msecondsElapsed = endTime - startTime;
		System.out.println("Elapsed time (milliseconds) = " + msecondsElapsed);	
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}
		ctx.close();

	}
	
	
	public static void sat8() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		long startTime = System.currentTimeMillis();
		long endTime = 0;
		float msecondsElapsed = 0;
		
		String v1 = "A";
		String v2 = "B";
		String v3 = "C";
		String v4 = "D";
		String v5 = "E";
		String v6 = "F";
		String v7 = "G";
		String v8 = "H";
		
		Expr A = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr B = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		Expr C = ctx.mkConst(ctx.mkSymbol(v3), ctx.mkStringSort());
		Expr D = ctx.mkConst(ctx.mkSymbol(v4), ctx.mkStringSort());
		Expr E = ctx.mkConst(ctx.mkSymbol(v5), ctx.mkStringSort());
		Expr F = ctx.mkConst(ctx.mkSymbol(v6), ctx.mkStringSort());
		Expr G = ctx.mkConst(ctx.mkSymbol(v7), ctx.mkStringSort());
		Expr H = ctx.mkConst(ctx.mkSymbol(v8), ctx.mkStringSort());
		
		Expr AB = ctx.mkConcat((SeqExpr) A, (SeqExpr)B);
		Expr CD = ctx.mkConcat((SeqExpr) C, (SeqExpr)D);
		Expr EF = ctx.mkConcat((SeqExpr) E, (SeqExpr)F);
		Expr GH = ctx.mkConcat((SeqExpr) G, (SeqExpr)H);

		
		ReExpr a = ctx.mkToRe(ctx.mkString("a"));
		ReExpr b = ctx.mkToRe(ctx.mkString("b"));
		ReExpr c = ctx.mkToRe(ctx.mkString("c"));
		ReExpr d = ctx.mkToRe(ctx.mkString("d"));
		
		ReExpr ab_3 = ctx.mkConcat(a,b,a,b,a,b);
		ReExpr ba_3 = ctx.mkConcat(b,a,b,a,b,a);
		 
		ReExpr a_star = ctx.mkStar(a);
		
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)AB, ab_3);
		BoolExpr mem_const2 = ctx.mkInRe((SeqExpr)CD, ba_3);
		BoolExpr mem_const3 = ctx.mkInRe((SeqExpr)EF, a_star);
		BoolExpr mem_const4 = ctx.mkInRe((SeqExpr)GH, b);
				
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)A));
		IntExpr lhs_len_const2 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)B));
		
		BoolExpr len_const1 = ctx.mkLe(lhs_len_const1, ctx.mkInt(3));
		BoolExpr len_const2 = ctx.mkLe(lhs_len_const2, ctx.mkInt(3));
		
		Expr lhs_eq1 = (SeqExpr) A;
		Expr rhs_eq1 = (SeqExpr) D;
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1);
		Expr lhs_eq2 = (SeqExpr) B;
		Expr rhs_eq2 = (SeqExpr) C;
		BoolExpr eq2 = ctx.mkEq(lhs_eq2, rhs_eq2);
		
		// add membership constraints
		solver.add(mem_const1);
		solver.add(mem_const2);
		solver.add(mem_const3);
		solver.add(mem_const4);
		// add length constraints
		solver.add(len_const1);
		solver.add(len_const2);
		
		// add equality constraints
		solver.add(eq1);
		solver.add(eq2);
		
		Status st = solver.check();
		
		endTime = System.currentTimeMillis();
		msecondsElapsed = endTime - startTime;
		System.out.println("Elapsed time (milliseconds) = " + msecondsElapsed);	
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}

	}
	
	
	public static void sat6() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		long startTime = System.currentTimeMillis();
		long endTime = 0;
		float msecondsElapsed = 0;
		
		String v1 = "x";
		String v2 = "y";
		String v3 = "z";
		String v4 = "A";
		String v5 = "B";
		String v6 = "C";
		
		Expr x = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr y = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		Expr z = ctx.mkConst(ctx.mkSymbol(v3), ctx.mkStringSort());
		Expr A = ctx.mkConst(ctx.mkSymbol(v4), ctx.mkStringSort());
		Expr B = ctx.mkConst(ctx.mkSymbol(v5), ctx.mkStringSort());
		Expr C = ctx.mkConst(ctx.mkSymbol(v6), ctx.mkStringSort());
		
		Expr ABC = ctx.mkConcat((SeqExpr) A, (SeqExpr)B, (SeqExpr)C);
		Expr xyz = ctx.mkConcat((SeqExpr) x, (SeqExpr)y, (SeqExpr)z);
		Expr yz = ctx.mkConcat((SeqExpr) y, (SeqExpr)z);

		
		ReExpr a = ctx.mkToRe(ctx.mkString("a"));
		ReExpr b = ctx.mkToRe(ctx.mkString("b"));
		ReExpr c = ctx.mkToRe(ctx.mkString("c"));
		ReExpr d = ctx.mkToRe(ctx.mkString("d"));
		
		ReExpr ab = ctx.mkConcat(a,b);
		ReExpr abc_union = ctx.mkUnion(a,b,c);
		ReExpr ab_c_union = ctx.mkUnion(ab,c);
		
		ReExpr abc_union_plus = ctx.mkPlus(abc_union); 
		ReExpr ab_c_union_plus = ctx.mkPlus(ab_c_union); 
		ReExpr a_plus = ctx.mkPlus(a); 
		ReExpr b_star = ctx.mkStar(b);
		
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)ABC, abc_union_plus);
		BoolExpr mem_const2 = ctx.mkInRe((SeqExpr)xyz, abc_union_plus);
		BoolExpr mem_const3 = ctx.mkInRe((SeqExpr)yz, ab_c_union_plus);
		BoolExpr mem_const4 = ctx.mkInRe((SeqExpr)x, a_plus);
		BoolExpr mem_const5 = ctx.mkInRe((SeqExpr)y, b_star);
				
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)A)),
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)B)),
				ctx.mkMul(ctx.mkInt(-1), ctx.mkLength((SeqExpr)C)));
		IntExpr lhs_len_const2 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)C)),
				ctx.mkMul(ctx.mkInt(-2), ctx.mkLength((SeqExpr)B)));
		
		BoolExpr len_const1 = ctx.mkEq(lhs_len_const1, ctx.mkInt(0));
		BoolExpr len_const2 = ctx.mkGe(lhs_len_const2, ctx.mkInt(1));
		
		Expr lhs_eq1 = (SeqExpr) B;
		Expr rhs_eq1 = (SeqExpr) y;
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1); 
		
		// add membership constraints
		solver.add(mem_const1);
		solver.add(mem_const2);
		solver.add(mem_const3);
		solver.add(mem_const4);
		solver.add(mem_const5);
		
		// add length constraints
		solver.add(len_const1);
		solver.add(len_const2);
		
		// add equality constraints
		solver.add(eq1);
		
		Status st = solver.check();
		
		endTime = System.currentTimeMillis();
		msecondsElapsed = endTime - startTime;
		System.out.println("Elapsed time (milliseconds) = " + msecondsElapsed);	
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}

	}
	
	
	public static void sat4() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		long startTime = System.currentTimeMillis();
		long endTime = 0;
		float msecondsElapsed = 0;
		
		String v1 = "x";
		String v2 = "y";
		String v3 = "z";
		String v4 = "w";
		
		Expr x = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr y = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		Expr z = ctx.mkConst(ctx.mkSymbol(v3), ctx.mkStringSort());
		Expr w = ctx.mkConst(ctx.mkSymbol(v4), ctx.mkStringSort());
		
		Expr xy = ctx.mkConcat((SeqExpr) x, (SeqExpr)y);
		Expr zw = ctx.mkConcat((SeqExpr) z, (SeqExpr)w);

		
		ReExpr a = ctx.mkToRe(ctx.mkString("a"));
		ReExpr b = ctx.mkToRe(ctx.mkString("b"));
		ReExpr c = ctx.mkToRe(ctx.mkString("c"));
		ReExpr d = ctx.mkToRe(ctx.mkString("d"));
		
		ReExpr ab = ctx.mkConcat(a,b);
		ReExpr cd = ctx.mkConcat(c,d);
		
		ReExpr ab_plus = ctx.mkPlus(ab); 
		ReExpr cd_star = ctx.mkStar(cd);
		
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)xy, ab_plus);
		BoolExpr mem_const2 = ctx.mkInRe((SeqExpr)zw, cd_star);
				
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)y));
		IntExpr lhs_len_const2 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)x));
		IntExpr lhs_len_const3 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)w));
		IntExpr lhs_len_const4 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)z));
		
		BoolExpr len_const1 = ctx.mkLt(lhs_len_const1, ctx.mkInt(2));
		BoolExpr len_const2 = ctx.mkGe(lhs_len_const2, ctx.mkInt(4));
		BoolExpr len_const3 = ctx.mkLt(lhs_len_const3, ctx.mkInt(3));
		BoolExpr len_const4 = ctx.mkEq(lhs_len_const4, ctx.mkInt(4));
		
		Expr lhs_eq1 = ctx.mkConcat((SeqExpr) x, (SeqExpr)y);
		Expr rhs_eq1 = ctx.mkConcat((SeqExpr) y, (SeqExpr)x);
		Expr lhs_eq2 = ctx.mkConcat((SeqExpr) z, (SeqExpr)w);
		Expr rhs_eq2 = ctx.mkConcat((SeqExpr) w, (SeqExpr)z);
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1); 
		BoolExpr eq2 = ctx.mkEq(lhs_eq2, rhs_eq2); 
		
		// add membership constraints
		solver.add(mem_const1);
		solver.add(mem_const2);
		
		// add length constraints
		solver.add(len_const1);
		solver.add(len_const2);
		solver.add(len_const3);
		solver.add(len_const4);
		
		// add equality constraints
		solver.add(eq1);
		solver.add(eq2);
		
		Status st = solver.check();
		
		endTime = System.currentTimeMillis();
		msecondsElapsed = endTime - startTime;
		System.out.println("Elapsed time (milliseconds) = " + msecondsElapsed);	
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}

	}
	
	public static void sat3() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		String v1 = "A";
		String v2 = "B";
		String v3 = "C";
		String v4 = "D";
		
		Expr A = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr B = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		Expr C = ctx.mkConst(ctx.mkSymbol(v3), ctx.mkStringSort());
		Expr D = ctx.mkConst(ctx.mkSymbol(v4), ctx.mkStringSort());
		
		ReExpr a = ctx.mkToRe(ctx.mkString("a"));
		ReExpr b = ctx.mkToRe(ctx.mkString("b"));
		
		ReExpr a_plus = ctx.mkPlus(a); 
		ReExpr b_plus = ctx.mkPlus(b); 
		
		Expr lhs_eq1 = ctx.mkConcat((SeqExpr) A, (SeqExpr)C);
		Expr rhs_eq1 = ctx.mkConcat((SeqExpr) B, (SeqExpr)D);
		
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)A, a_plus);
		BoolExpr mem_const2 = ctx.mkInRe((SeqExpr)B, b_plus);
		BoolExpr mem_const3 = ctx.mkInRe((SeqExpr)C, a_plus);
		BoolExpr mem_const4 = ctx.mkInRe((SeqExpr)D, b_plus);
		
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(-1), ctx.mkLength((SeqExpr)A)),
				ctx.mkMul(ctx.mkInt(3), ctx.mkLength((SeqExpr)D)));
		
		BoolExpr len_const1 = ctx.mkLt(lhs_len_const1, ctx.mkInt(8));
		
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1); 
		
		
		solver.add(mem_const1);
		solver.add(mem_const2);
		solver.add(mem_const3);
		solver.add(mem_const4);
		solver.add(len_const1);
		solver.add(eq1);
		
		Status st = solver.check();
		
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}

	}
	
	public static void sat2() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		long startTime = System.currentTimeMillis();
		long endTime = 0;
		float msecondsElapsed = 0;
		
		String v1 = "x";
		String v2 = "y";
		
		Expr x = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr y = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		
		Expr xy = ctx.mkConcat((SeqExpr) x, (SeqExpr)y);

		
		ReExpr a = ctx.mkToRe(ctx.mkString("a"));
		ReExpr b = ctx.mkToRe(ctx.mkString("b"));
		
		ReExpr ab = ctx.mkConcat(a,b);
		
		ReExpr ab_plus = ctx.mkPlus(ab); 
		
		Expr lhs_eq1 = ctx.mkConcat((SeqExpr) x, (SeqExpr)y);
		Expr rhs_eq1 = ctx.mkConcat((SeqExpr) y, (SeqExpr)x);
		
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)xy, ab_plus);
		
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)y));
		IntExpr lhs_len_const2 = (IntExpr) ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)x));
		
		BoolExpr len_const1 = ctx.mkLt(lhs_len_const1, ctx.mkInt(6));
		BoolExpr len_const2 = ctx.mkEq(lhs_len_const2, ctx.mkInt(4));
		
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1); 
		
		// add membership constraints
		solver.add(mem_const1);
		
		// add length constraints
		solver.add(len_const1);
		solver.add(len_const2);
		
		// add equality constraints
		solver.add(eq1);
		
		Status st = solver.check();
		
		endTime = System.currentTimeMillis();
		msecondsElapsed = endTime - startTime;
		System.out.println("Elapsed time (milliseconds) = " + msecondsElapsed);	
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}

	}
	
	public static void sat1() {
		final Context ctx = new Context();
		final Solver solver = ctx.mkSimpleSolver();
		
		String v1 = "x";
		String v2 = "y";
		String v3 = "m";
		String v4 = "w";
		String v5 = "z";
		
		Expr x = ctx.mkConst(ctx.mkSymbol(v1), ctx.mkStringSort());
		Expr y = ctx.mkConst(ctx.mkSymbol(v2), ctx.mkStringSort());
		Expr m = ctx.mkConst(ctx.mkSymbol(v3), ctx.mkStringSort());
		Expr w = ctx.mkConst(ctx.mkSymbol(v4), ctx.mkStringSort());
		Expr z = ctx.mkConst(ctx.mkSymbol(v5), ctx.mkStringSort());
		
		ReExpr a = ctx.mkToRe(ctx.mkString("a"));
		ReExpr b = ctx.mkToRe(ctx.mkString("b"));
		ReExpr c = ctx.mkToRe(ctx.mkString("c"));
		ReExpr abc_union = ctx.mkUnion(a, b, c); 
		ReExpr ab_union = ctx.mkUnion(a, b);
		Expr xym = ctx.mkConcat((SeqExpr) x, (SeqExpr)y, (SeqExpr)m);
		Expr zw = ctx.mkConcat((SeqExpr) z, (SeqExpr)w);
		Expr lhs_eq1 = ctx.mkConcat((SeqExpr) z, (SeqExpr)w, (SeqExpr)m);
		Expr rhs_eq1 = ctx.mkConcat((SeqExpr) m, (SeqExpr)y, (SeqExpr)y);
		Expr lhs_eq2 = ctx.mkConcat((SeqExpr) m, (SeqExpr)y);
		Expr rhs_eq2 = ctx.mkConcat((SeqExpr)w, (SeqExpr)m);
		
		ReExpr abc_union_star = ctx.mkStar(abc_union);
		ReExpr ab_union_star = ctx.mkStar(ab_union);
		BoolExpr mem_const1 = ctx.mkInRe((SeqExpr)xym, abc_union_star);
		BoolExpr mem_const2 = ctx.mkInRe((SeqExpr)m, ctx.mkStar(b));
		BoolExpr mem_const3 = ctx.mkInRe((SeqExpr)zw, ab_union_star);
		
		IntExpr lhs_len_const1 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)x)),
				ctx.mkMul(ctx.mkInt(-1), ctx.mkLength((SeqExpr)m)));
		IntExpr lhs_len_const2 = (IntExpr) ctx.mkAdd(
				ctx.mkMul(ctx.mkInt(2), ctx.mkLength((SeqExpr)w)),
                ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)z)),
                ctx.mkMul(ctx.mkInt(1), ctx.mkLength((SeqExpr)y)));
		IntExpr lhs_len_const3 = (IntExpr) ctx.mkAdd(
                ctx.mkMul(ctx.mkInt(3), ctx.mkLength((SeqExpr)x)));
		
		BoolExpr len_const1 = ctx.mkGt(lhs_len_const1, ctx.mkInt(1));
		BoolExpr len_const2 = ctx.mkLt(lhs_len_const2, ctx.mkInt(10));
		BoolExpr len_const3 = ctx.mkGe(lhs_len_const3, ctx.mkInt(9));
		
		BoolExpr eq1 = ctx.mkEq(lhs_eq1, rhs_eq1); 
		BoolExpr eq2 = ctx.mkEq(lhs_eq2, rhs_eq2); 
		
		
		solver.add(mem_const1);
		solver.add(mem_const2);
		solver.add(mem_const3);
		solver.add(len_const1);
		solver.add(len_const2);
		solver.add(len_const3);
		solver.add(eq1);
		solver.add(eq2);
		
		Status st = solver.check();
		
		System.out.println("NumAssertions = " + solver.getNumAssertions());
		System.out.println("SATISFIABLE :" + st.equals(Status.SATISFIABLE));
		System.out.println(solver.toString());
		if ( st.equals(Status.SATISFIABLE)) {
			Model model = solver.getModel();
			System.out.println(model.toString());				
		}
	}
}