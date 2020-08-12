import java.util.*;
import java.util.stream.Collectors;

import dk.brics.automaton.*;
import com.microsoft.z3.*;

/**
 * @author hamid
 *
 */
/**
 * @author hamid
 *
 */
public class DemoProgram {

	public static void main(String[] args) {
		readUserInput();
		//testSat();
	}
	
	public static void readUserInput() {
		// for each disjunct in the user input:
		//    example: ((abc in A1) and (len(d) < 5) and (fa not in A2) and (gbe in A3))
		// make two parts, one with only string constraints, the other with length constraints
		// memberCons = ((abc in A1) and (fa not in A2) and (gbe in A3))
		// lenCons = len(d) < 5
		// 
		// 		vars = list of the variables ordered according to their appearance in the formulas
		//			for example if the disjunct is:
		//					
		//
		String lhsOfMemCons1 = "ab";
		String lhsOfMemCons2 = "b";
		String lhsOfMemCons3 = "db";
		String lhsOfMemCons4 = "c";
		String lhsOfMemCons5 = "eac";
		RegExp r1 = new RegExp("(w|z)+");
		RegExp r2 = new RegExp("(wz|zw)*");
		RegExp r3 = new RegExp("w|z");
		RegExp r4 = new RegExp("(w|z|wz)*");
		RegExp r5 = new RegExp("z+");
		Automaton rhsOfMemCons1 = r1.toAutomaton();
		Automaton rhsOfMemCons2 = r2.toAutomaton();
		Automaton rhsOfMemCons3 = r3.toAutomaton();
		Automaton rhsOfMemCons4 = r4.toAutomaton();
		Automaton rhsOfMemCons5 = r5.toAutomaton();
		List<String> lhsOfMemCons = new ArrayList<String> ();
		List<Automaton> rhsOfMemCons = new ArrayList<Automaton> ();
		lhsOfMemCons.add(0, lhsOfMemCons1);
		lhsOfMemCons.add(1, lhsOfMemCons2);
		lhsOfMemCons.add(2, lhsOfMemCons3);
		lhsOfMemCons.add(3, lhsOfMemCons4);
		lhsOfMemCons.add(4, lhsOfMemCons5);
		//System.out.println("lhsOfMembershipCons: " + lhsOfMembershipCons);
		rhsOfMemCons.add(0, rhsOfMemCons1);
		rhsOfMemCons.add(1, rhsOfMemCons2);
		rhsOfMemCons.add(2, rhsOfMemCons3);
		rhsOfMemCons.add(3, rhsOfMemCons4);
		rhsOfMemCons.add(4, rhsOfMemCons5);	
		//System.out.println("rhsOfMembershipCons: " + rhsOfMembershipCons);
		
		/******************************************************************************
		 * the length constraint (2y - 4x + w >= 2) is expressed as follows: 
		 *      lhsOfLenCon = {'x'=-4, 'y'=2, 'w'=1}
		 *      rhsOfLenCon = 2
		 *      relLhs2RhsOfLenCon = IntegerRelation.GREATEREQUAL
		 ******************************************************************************      
		 */   
		List<Map<Character, Integer>> lhsOfLenCons = new ArrayList<Map<Character, Integer>> ();
		List<Integer> rhsOfLenCons = new ArrayList<Integer> ();
		List<IntegerRelation> relLhs2RhsOfLenCons = new ArrayList<IntegerRelation> ();
		getLengthConstraints(lhsOfLenCons, relLhs2RhsOfLenCons, rhsOfLenCons);
		System.out.println("lhsOfLenCons = " + lhsOfLenCons);
		System.out.println("rhsOfLenCons = " + rhsOfLenCons);
		System.out.println("relLhs2RhsOfLenCons = " + relLhs2RhsOfLenCons);
		/***********************************************************************************/
		
		/******************************************************************************
		 * the equality constraint (ab = cd) is expressed as follows: 
		 *      lhsOfEqDeqCon = "ab"
		 *      rhsOfEqDeqCon = "cd"
		 *      relLhs2RhsOfEqDeqCon = EqualityRelation.EQUAL
		 ******************************************************************************      
		 */ 
		List<String> lhsEqDeqCons = new ArrayList<String> ();
		List<String> rhsEqDeqCons = new ArrayList<String> ();
		List<EqualityRelation> relLhs2RhsOfEqDeqCons = new ArrayList<EqualityRelation> ();
		getEqDeqConstraints(lhsEqDeqCons, relLhs2RhsOfEqDeqCons, rhsEqDeqCons);
		System.out.println("lhsEqDeqCons = " + lhsEqDeqCons);
		System.out.println("rhsEqDeqCons = " + rhsEqDeqCons);
		System.out.println("relLhs2RhsOfEqDeqCons = " + relLhs2RhsOfEqDeqCons);
		/***********************************************************************************/
		
		ArrayList<ArrayList<Map<Integer, Integer> > > refinedIntegerArithDnf =
				new ArrayList<ArrayList<Map<Integer, Integer> > > ();
		ArrayList<Character> variables = new ArrayList<Character> ();
		processMembershipConstraints(variables, refinedIntegerArithDnf, lhsOfMemCons, rhsOfMemCons);
		System.out.println("variables: " + variables);
		System.out.println("refinedIntegerArithDnf: " + refinedIntegerArithDnf);
		if(refinedIntegerArithDnf.size() == 0) {
			System.out.println("memebership constraints are UNSAT");
		}
		else {		
			final Context context = new Context();
			final Solver solver = context.mkSimpleSolver();
			Map<Character, IntExpr> lengthVariables = makeLengthVariables(context, variables);
			System.out.println("lengthVariables = " + lengthVariables);
			addLengthConstraintsToSolver(lhsOfLenCons, relLhs2RhsOfLenCons, rhsOfLenCons, 
					                     lengthVariables, context, solver);
			System.out.println("solver after adding length constraints= " + solver.toString());
			//Status st = solver.check();
			// if length constraints alone are satisfiable, we check the membership constraints
			if (solver.check().equals(Status.SATISFIABLE)) {
				System.out.println("Length constraints are SATISFIABLE");
				// the remaining code should go in here
				int previousSatIntegerArithDisjId = -1;
				//solver.push();
				int nextSatIntegerArithDisjId = getNextSatIntegerArithDisjId(refinedIntegerArithDnf, 
						                    lengthVariables, variables, context, solver, 
						                    previousSatIntegerArithDisjId);
				System.out.println("nextSatIntegerArithDisjId = " + nextSatIntegerArithDisjId);
				System.out.println("solver after adding membership constraints= " + solver.toString());
				
				
				//solver.pop();
				
				underApproximation(variables, lhsEqDeqCons, relLhs2RhsOfEqDeqCons, rhsEqDeqCons);
				
			}
			
		}
		
	}
	
	private static void underApproximation(ArrayList<Character> u_variables, List<String> lhsEqDeqCons, List<EqualityRelation> relLhs2RhsOfEqDeqCons, List<String> rhsEqDeqCons) {
		System.out.println("****************************************************************");
		System.out.println("****************************************************************");
		System.out.println("The UnderApproximation function");
		System.out.println("The lhsEqDeqCons: " + lhsEqDeqCons);
		System.out.println("The relLhs2RhsOfEqDeqCons: " + relLhs2RhsOfEqDeqCons);
		System.out.println("The rhsEqDeqCons: " + rhsEqDeqCons);
		// u_variables should be substituted with variable. it is used here for testing the
		// underApproximation function implementation
		//ArrayList<Character> u_variables = new ArrayList<Character> ();
		// u_variables[i] is split into a number of variables. This number is u_variables_split_count[i]
		ArrayList<Integer> u_variables_split_count = new ArrayList<Integer> ();
		Map<Character, ArrayList<String> > u_variables_split = new HashMap<Character, ArrayList<String> > ();
		
		System.out.println("u_variables: " + u_variables);
		ArrayList<ArrayList<Integer>> lengthPermutations = new ArrayList<ArrayList<Integer>> ();
		int K_parameter = 5;
		for (ArrayList<Integer> permutation: getPermutations(K_parameter, u_variables.size())) {
			List<Integer> lengthPermutation = permutation.stream().map(number -> number + 1). 
			        collect(Collectors.toList());
			lengthPermutations.add((ArrayList<Integer>) lengthPermutation);			
		}
		System.out.println("lengthPermutations: " + lengthPermutations);
		u_variables_split_count = lengthPermutations.get(7);
		System.out.println("u_variables_split_count: " + u_variables_split_count);
		for (int i = 0; i < u_variables.size(); i++) {
			Character c = u_variables.get(i);
			int split_count = u_variables_split_count.get(i);
			ArrayList<String> c_split_into = new ArrayList<String> ();
			for (int j = 1; j <= split_count; j++) {
				c_split_into.add(c.toString() + j);				
			}
			u_variables_split.put(c, c_split_into);
		}
		System.out.println("u_variables_split: " + u_variables_split);
		// fixedVars should contain the value(s) for each variable,
		// for example fixedVars[x1] = {y2,z3} means that x1 = y2 and x1 = z3
		// fixedVars[x] = {.., x, ..} is not allowed
		Map<String, HashSet<String> > fixedVars = new HashMap<String, HashSet<String> > ();
		for (Character c: u_variables) {
			for (String s: u_variables_split.get(c) ) {
				HashSet<String> s_values = new HashSet<String> ();
				fixedVars.put(s, s_values);					
			}		
		}
		//System.out.println("fixedVars: " + fixedVars);
		//System.out.println("fixedVars size: " + fixedVars.size());
		for (int id = 0; id < lhsEqDeqCons.size(); id++) {
			// each variable is expressed by its split variables,
			// i.e x = u_variables[i] is written as u_variables_split[x]
			ArrayList<String> splitLhsEqDeqConsI = new ArrayList<String> ();
			ArrayList<String> splitRhsEqDeqConsI = new ArrayList<String> ();
			String lhsEqDeqConsI = lhsEqDeqCons.get(id);
			String rhsEqDeqConsI = rhsEqDeqCons.get(id);
			for (int i = 0; i < lhsEqDeqConsI.length(); i++) {
				Character c = lhsEqDeqConsI.charAt(i);
				ArrayList<String> c_split = u_variables_split.get(c);
				for (int j = 0; j < c_split.size(); j++) {
					splitLhsEqDeqConsI.add(c_split.get(j));				
				}
			}
			for (int i = 0; i < rhsEqDeqConsI.length(); i++) {
				Character c = rhsEqDeqConsI.charAt(i);
				ArrayList<String> c_split = u_variables_split.get(c);
				for (int j = 0; j < c_split.size(); j++) {
					splitRhsEqDeqConsI.add(c_split.get(j));				
				}
			}
			//System.out.println("splitLhsEqDeqConsI: " + splitLhsEqDeqConsI);
			//System.out.println("splitRhsEqDeqConsI: " + splitRhsEqDeqConsI);
			fixVariables(fixedVars, splitLhsEqDeqConsI, splitRhsEqDeqConsI);	
		}
		System.out.println("fixedVars: " + fixedVars);
		//System.out.println("Permutations: " + getPermutations(2,2)); 
		
	}
	
	// this method should update fixedVars with the values obtained from the equality 
	// given by splitLhsEqDeqCons and splitRhsEqDeqCons
	private static void fixVariables(Map<String, HashSet<String>> fixedVars, ArrayList<String> splitLhsEqDeqCons,
			ArrayList<String> splitRhsEqDeqCons) {
		// TODO Auto-generated method stub
		// shortSide should be in the left side of the equality
		ArrayList<String> shortSide;
		ArrayList<String> longSide;
		int shortSize, longSize;
		if (splitLhsEqDeqCons.size() <= splitRhsEqDeqCons.size()) {
			shortSide = splitLhsEqDeqCons;
			longSide = splitRhsEqDeqCons;			
		}
		else {
			shortSide = splitRhsEqDeqCons;
			longSide = splitLhsEqDeqCons;			
		}
		shortSize = shortSide.size();
		longSize = longSide.size();
		//System.out.println("shortSide: " + shortSide);
		//System.out.println("longSide: " + longSide);
		for (int i = 0; i < shortSize; i++) {
			String leftStr = shortSide.get(i);
			String rightStr = longSide.get(i);
			if (!leftStr.equals(rightStr)) {
				fixedVars.get(leftStr).add(rightStr);
			}
		}
		for (int i = shortSize; i < longSize; i++) {
			String rightStr = longSide.get(i);
			fixedVars.get(rightStr).add("EPSILON");
		}
	}

	private static int getNextSatIntegerArithDisjId(ArrayList<ArrayList<Map<Integer, Integer>>> refinedIntegerArithDnf,
			Map<Character, IntExpr> lengthVariables, ArrayList<Character> variables, Context context, Solver solver,
			int previousSatIntegerArithDisjId) {
		// TODO Auto-generated method stub
		// the previous IntegerArithDisj didn't result in SAT constraints, so 
		// have to examine the next IntegerArithDisj
		int nextIntegerArithDisjId = previousSatIntegerArithDisjId + 1;
		while(nextIntegerArithDisjId < refinedIntegerArithDnf.size()) {	 
			ArrayList<Map<Integer, Integer>> nextIntegerArithDisj = 
					refinedIntegerArithDnf.get(nextIntegerArithDisjId);
			solver.push();
			boolean isSat = testSat(nextIntegerArithDisj, lengthVariables, variables, context, solver);
			System.out.println("isSat = " + isSat);
			if (isSat) {
				return nextIntegerArithDisjId;				
			}
			else {
				solver.pop();
				nextIntegerArithDisjId = nextIntegerArithDisjId + 1;
			}
		}
		return nextIntegerArithDisjId;
	}

	
	public static boolean testSat(ArrayList<Map<Integer, Integer> >  lassoList, 
			Map<Character, IntExpr> lengthVariables, ArrayList<Character> variables,
			Context ctx, Solver solver) {
		// ArrayList<ArrayList<Map<Integer, Integer> > > integerArithDnf 
		// [{0=0}, {0=2, 1=1, 2=1}, {1=3}, {1=0, 2=2}]
		// this represents the following:
		// (len(var0) = 0) and (len(var1) = 2i or len(var1) = 1 + i or len(var1) = 2 + i) and
		// (len(var2) = 1 + 3i) and (len(var3) = 1 or len(var3) = 2 + 2i)
		// note that i above is not essentially the same in each equation
		//System.out.println("lassoList = " + lassoList);
		ArrayList<BoolExpr> linearConstraints = new ArrayList<BoolExpr> ();
		// the length constraint for each var is : len(var) = k + v*i
		ArrayList<IntExpr> vars = new ArrayList<IntExpr> ();
		for (Character c: lengthVariables.keySet()) {
			IntExpr var = lengthVariables.get(c);
			// each var >= 0
			BoolExpr nonNegativeVar = ctx.mkGe(var, ctx.mkInt(0));
			solver.add(nonNegativeVar);
			//System.out.println("nonNegativeVar: " + nonNegativeVar);
			
		}
		//System.out.println("variables: " + vars);
		
		// Example: varKIMaps[0] = {0=i_0_0, 1=i_0_1, 2=i_0_2}
		// means that len(var_0) = 0+ v0*i_0_0 or len(var_0) = 1+ v1*i_0_1 or 
		//            len(var_0) = 2+ v2*i_0_2 where lasso(var_0) = {0=v0, 1=v1, 2=v2}
		ArrayList<Map<Integer, IntExpr> >  varKIMaps = new ArrayList<Map<Integer, IntExpr> > ();
		for (int i = 0; i < lassoList.size(); i++) {
			Map<Integer, Integer> lasso = lassoList.get(i);
			Map<Integer, IntExpr> varKIMap = new HashMap<Integer, IntExpr> ();
			for (int k: lasso.keySet()) {
				String s = "i_" + Integer.toString(i) + "_" + Integer.toString(k);
				IntExpr iVar = ctx.mkIntConst(s); 
				varKIMap.put(k, iVar);									
				BoolExpr nonNegativeI = ctx.mkGe(iVar, ctx.mkInt(0));
				solver.add(nonNegativeI);
			}
			varKIMaps.add(i, varKIMap);
		}
		//System.out.println("i_variables: " + varKIMaps);
		// to do: add the constraint that variables are >= to 0
		for (int i = 0; i < lassoList.size(); i++) {
			IntExpr var = lengthVariables.get(variables.get(i));
			Map<Integer, Integer> lasso = lassoList.get(i);
			//System.out.println(lasso);
			Map<Integer, IntExpr> varKIMap = varKIMaps.get(i);
			Set<Integer> varKs = lasso.keySet();
			if (varKs.size() == 1) {
				for (int k: varKs) {
					IntExpr k_term = ctx.mkInt(k);
					IntExpr vi_term = (IntExpr) ctx.mkMul(ctx.mkInt(lasso.get(k)), varKIMap.get(k));
					BoolExpr linearConstraint = ctx.mkEq(var, ctx.mkAdd(k_term, vi_term));	
					linearConstraints.add(i, linearConstraint);
					solver.add(linearConstraint);
					//System.out.println(linearConstraint);					
				}			
			}
			else {
				BoolExpr linearConstraint = ctx.mkBool(false);
				for (int k: varKs) {
					IntExpr k_term = ctx.mkInt(k);
					IntExpr vi_term = (IntExpr) ctx.mkMul(ctx.mkInt(lasso.get(k)), varKIMap.get(k));
					BoolExpr linearConstraintDisj = ctx.mkEq(var, ctx.mkAdd(k_term, vi_term));
					linearConstraint = ctx.mkOr(linearConstraint, linearConstraintDisj);
				}
				linearConstraints.add(i, linearConstraint);	
				solver.add(linearConstraint);
				//System.out.println(linearConstraint);
			}
		}
		System.out.println("solver in the testSat function: " + solver);
		Status satStatus = solver.check();
		boolean isSat = satStatus.equals(Status.SATISFIABLE);
		//System.out.println("Constraints are SAT: " + isSat);
		//final Model model = solver.getModel();
		//System.out.println(model.toString());
		//System.out.println("linearConstraints: " + linearConstraints);
		//ctx.close();
		return isSat;
	}

	private static void addLengthConstraintsToSolver(List<Map<Character, Integer>> lhsOfLenCons,
			List<IntegerRelation> relLhs2RhsOfLenCons, List<Integer> rhsOfLenCons,
			Map<Character, IntExpr> lengthVariables, Context context, Solver solver) {
		// TODO Auto-generated method stub
		for (int i = 0; i < lhsOfLenCons.size(); i++) {
			Map<Character, Integer> lhsOfLenConsI = lhsOfLenCons.get(i);
			IntegerRelation relLhs2RhsOfLenConsI = relLhs2RhsOfLenCons.get(i);
			int rhsOfLenConsI = rhsOfLenCons.get(i);
			IntExpr lhsI = context.mkInt(0);
			IntExpr rhsI = context.mkInt(rhsOfLenConsI);
			BoolExpr b = context.mkBool(true);
			for (Character c: lhsOfLenConsI.keySet()) {
				IntExpr x = lengthVariables.get(c);
				IntExpr a = context.mkInt(lhsOfLenConsI.get(c));
				lhsI = (IntExpr) context.mkAdd(context.mkMul(x,a), lhsI);
			}
			switch (relLhs2RhsOfLenConsI) {
			case EQUAL:
				b = context.mkEq(lhsI, rhsI);
				break;
			case NOTEQUAL:
				b = context.mkNot(context.mkEq(lhsI, rhsI));
				break;
			case GREATER:
				b = context.mkGt(lhsI, rhsI);
				break;
			case GREATEREQUAL:
				b = context.mkGe(lhsI, rhsI);
				break;
			case LESS:
				b = context.mkLt(lhsI, rhsI);
				break;
			case LESSEQUAL:
				b = context.mkLe(lhsI, rhsI);
				break;	
			}
			solver.add(b);
		}
	}

	private static Map<Character, IntExpr> makeLengthVariables(Context context, ArrayList<Character> variables) {
		// TODO Auto-generated method stub
		Map<Character, IntExpr> lengthVariables = new HashMap<Character, IntExpr> ();
		for (Character c: variables) {
			IntExpr x = context.mkIntConst("len_" + Character.toString(c));
			lengthVariables.put(c, x);
		}
		return lengthVariables;
	}

	private static void getEqDeqConstraints(List<String> lhsEqDeqCons, List<EqualityRelation> relLhs2RhsOfEqDeqCons,
			List<String> rhsEqDeqCons) {
		// TODO Auto-generated method stub
		String lhsEqDeqCons1, lhsEqDeqCons2;
		EqualityRelation relLhs2RhsOfEqDeqCons1, relLhs2RhsOfEqDeqCons2;
		String rhsEqDeqCons1, rhsEqDeqCons2;
		lhsEqDeqCons1 = "ac";
		rhsEqDeqCons1 = "be";
		relLhs2RhsOfEqDeqCons1 = EqualityRelation.EQUAL;
		lhsEqDeqCons.add(lhsEqDeqCons1);
		rhsEqDeqCons.add(rhsEqDeqCons1);
		relLhs2RhsOfEqDeqCons.add(relLhs2RhsOfEqDeqCons1);
		
		lhsEqDeqCons2 = "d";
		rhsEqDeqCons2 = "b";
		relLhs2RhsOfEqDeqCons2 = EqualityRelation.EQUAL;
		lhsEqDeqCons.add(lhsEqDeqCons2);
		rhsEqDeqCons.add(rhsEqDeqCons2);
		relLhs2RhsOfEqDeqCons.add(relLhs2RhsOfEqDeqCons2);
				
	}

	private static void getLengthConstraints(List<Map<Character, Integer>> lhsOfLenCons,
			List<IntegerRelation> relLhs2RhsOfLenCons, List<Integer> rhsOfLenCons) {
		// TODO Auto-generated method stub
		Map<Character, Integer> lhsOfLenCons1 = new HashMap<Character, Integer> ();
		Map<Character, Integer> lhsOfLenCons2 = new HashMap<Character, Integer> ();
		Map<Character, Integer> lhsOfLenCons3 = new HashMap<Character, Integer> ();
		int rhsOfLenCons1, rhsOfLenCons2, rhsOfLenCons3;
		IntegerRelation relLhs2RhsOfLenCons1, relLhs2RhsOfLenCons2, relLhs2RhsOfLenCons3;
	
		lhsOfLenCons1.put('b', 2);
		lhsOfLenCons1.put('a', -4);
		rhsOfLenCons1 = 5;
		relLhs2RhsOfLenCons1 = IntegerRelation.GREATER;
		lhsOfLenCons.add(lhsOfLenCons1);
		relLhs2RhsOfLenCons.add(relLhs2RhsOfLenCons1);
		rhsOfLenCons.add(rhsOfLenCons1);
		
		lhsOfLenCons2.put('a', 1);
		lhsOfLenCons2.put('b', 1);
		lhsOfLenCons2.put('c', 1);
		rhsOfLenCons2 = 8;
		relLhs2RhsOfLenCons2 = IntegerRelation.LESS;
		lhsOfLenCons.add(lhsOfLenCons2);
		relLhs2RhsOfLenCons.add(relLhs2RhsOfLenCons2);
		rhsOfLenCons.add(rhsOfLenCons2);
		
		lhsOfLenCons3.put('e', 1);
		rhsOfLenCons3 = 3;
		relLhs2RhsOfLenCons3 = IntegerRelation.GREATEREQUAL;
		lhsOfLenCons.add(lhsOfLenCons3);
		relLhs2RhsOfLenCons.add(relLhs2RhsOfLenCons3);
		rhsOfLenCons.add(rhsOfLenCons3);
	}

	private static void processMembershipConstraints(ArrayList<Character> variables,
			ArrayList<ArrayList<Map<Integer, Integer>>> refinedIntegerArithDnf, List<String> lhsOfMemCons,
			List<Automaton> rhsOfMemCons) {
		// TODO Auto-generated method stub
		Map<Integer, ArrayList<ArrayList<Automaton> > > simpleMembership = 
				getsimpleMembership(lhsOfMemCons,rhsOfMemCons);
		ArrayList<ArrayList<Automaton> > simpleMembershipDnf = 
				getsimpleMembershipDnf(simpleMembership);
		String lhsOfMemConsCombined = combinelhsOfMemCons(lhsOfMemCons);
		System.out.println("lhsOfMemConsCombined: " + lhsOfMemConsCombined);
		ArrayList<ArrayList<Integer> > equalVarIds = getEqualVarIds(lhsOfMemConsCombined);
		//System.out.println(equalVarIds);
		String vars = getVars(lhsOfMemConsCombined, equalVarIds);
		for (int i = 0; i < vars.length(); i++) {
			variables.add(i, vars.charAt(i));						
		}
		//System.out.println("vars: " + vars);
		ArrayList<ArrayList<Automaton> > simpleMembershipDnfIntersected = 
				intersectSimpleMembershipDnf(simpleMembershipDnf, equalVarIds);
		ArrayList<ArrayList<Automaton> > oneSymbolAutomataDnf = 
				getOneSymbolAutomataDnf(simpleMembershipDnfIntersected);
		//System.out.println(simpleMembershipDnfIntersected.size() == oneSymbolAutomataDnf.size());
		ArrayList<ArrayList<Map<Integer, Integer> > > unRefinedintegerArithDnf = 
				getIntegerArithDnf(oneSymbolAutomataDnf);
		refineIntegerArithDnf(unRefinedintegerArithDnf, refinedIntegerArithDnf);
	}

	private static void refineIntegerArithDnf(ArrayList<ArrayList<Map<Integer, Integer>>> integerArithDnf,
			ArrayList<ArrayList<Map<Integer, Integer> > > refinedIntegerArithDnf) {
		boolean isValid = true;
		int countImpossibleSols = 0;
		//ArrayList<ArrayList<Map<Integer, Integer>>> result = new ArrayList<ArrayList<Map<Integer, Integer> > > ();
		for (int i=0; i < integerArithDnf.size(); i++) {
			ArrayList<Map<Integer, Integer> > possibleSol = integerArithDnf.get(i);
			boolean isPossibleSol = true;
			for (int j = 0; j < possibleSol.size(); j++) {
				Map<Integer, Integer> lasso = possibleSol.get(j);
				if (lasso.containsKey(-1)) {
					if (lasso.keySet().size() > 1) {
						System.out.println("Error in lasso");
						isValid = false;
					}
					countImpossibleSols++;
					isPossibleSol = false;
					break;
				}
			}
			if (isPossibleSol) {
				refinedIntegerArithDnf.add(possibleSol);				
			}
		}
		//int x = integerArithDnf.size() - result.size();
		//boolean check = x == countImpossibleSols;
		//System.out.println("Check refineIntegerArithDnf is correct: " + check);
		//System.out.println("integerArithDnf size = " + integerArithDnf.size());
		//System.out.println("countImpossibleSols = " + countImpossibleSols);
		//System.out.println("refineIntegerArithDnf output: " + result);		
	}

	public static ArrayList<ArrayList<Map<Integer, Integer> > > getIntegerArithDnf
	                        (ArrayList<ArrayList<Automaton> > oneSymbolAutomataDnf) {
		ArrayList<ArrayList<Map<Integer, Integer> > > integerArithDnf = 
				new ArrayList<ArrayList<Map<Integer, Integer> > > ();
		for (int i = 0; i < oneSymbolAutomataDnf.size(); i++) {
			ArrayList<Automaton> automataConjunctions = oneSymbolAutomataDnf.get(i);
			ArrayList<Map<Integer, Integer> > integerArithConjunctions = new ArrayList<Map<Integer, Integer> > ();
			for (int j = 0; j < automataConjunctions.size(); j++) {
				Map<Integer, Integer> automataAsIntegerArith = lassoAsLinearConstraint(automataConjunctions.get(j));
				//System.out.println("Var " + j + " as linear: " + automataAsIntegerArith);
				integerArithConjunctions.add(automataAsIntegerArith);
			}
			integerArithDnf.add(integerArithConjunctions);									
		}
		return integerArithDnf;
	}
	
	public static ArrayList<ArrayList<Automaton> > getOneSymbolAutomataDnf
	                            (ArrayList<ArrayList<Automaton> > simpleMembershipDnfIntersected) {
		ArrayList<ArrayList<Automaton> > oneSymbolAutomataDnf = new ArrayList<ArrayList<Automaton> > ();
		// boolean areLassoAll = true;
		for (int i = 0; i < simpleMembershipDnfIntersected.size(); i++) {
			ArrayList<Automaton> automatonConjunctions = simpleMembershipDnfIntersected.get(i);
			ArrayList<Automaton> oneSymbolAutomataConjunctions = new ArrayList<Automaton> ();
			for (int j = 0; j < automatonConjunctions.size(); j++) {
				Automaton oneSymbolAutomaton = changeToOneSymbolAndMinimize(automatonConjunctions.get(j));
				oneSymbolAutomataConjunctions.add(oneSymbolAutomaton);
//				if (!testLasso(oneSymbolAutomaton)) {
//					areLassoAll = false;			
//				}
			}
			oneSymbolAutomataDnf.add(oneSymbolAutomataConjunctions);			
		}
		//System.out.println("All lasso: " + areLassoAll);
		return oneSymbolAutomataDnf;
	}
	
	public static ArrayList<ArrayList<Automaton> > intersectSimpleMembershipDnf
	              (ArrayList<ArrayList<Automaton> > simpleMembershipDnf, 
	            		  ArrayList<ArrayList<Integer> > equalVarIds) {
		ArrayList<ArrayList<Automaton> > simpleMembershipDnfIntersected = new ArrayList<ArrayList<Automaton> > ();
		if (equalVarIds.size() == 0) {
			simpleMembershipDnfIntersected = simpleMembershipDnf;						
		}
		else {
			simpleMembershipDnfIntersected = intersectAutomata(simpleMembershipDnf, equalVarIds);
		}
		return simpleMembershipDnfIntersected;
	}
	
	public static String getVars(String lhsOfMemConsCombined, ArrayList<ArrayList<Integer> > equalVarIds) {
		String vars = "";
		for (int i = 0; i < lhsOfMemConsCombined.length(); i++) {
			boolean hasBeenAdded = false;
			for (int j = 0; j < equalVarIds.size(); j++) {
				if (equalVarIds.get(j).indexOf(i) > 0) {
					hasBeenAdded = true;
					break;
				}				
			}
			if (!hasBeenAdded) {
				vars = vars + lhsOfMemConsCombined.charAt(i);								
			}
		}
		return vars;
	}
	
	public static ArrayList<ArrayList<Integer> > getEqualVarIds(String lhsOfMemConsCombined) {
		ArrayList<ArrayList<Integer> > equalVarIds = new ArrayList<ArrayList<Integer> > ();
		List<Boolean> idHasBeenAdded = new ArrayList<Boolean> ();
		for (int i = 0; i < lhsOfMemConsCombined.length(); i++) {
			idHasBeenAdded.add(false);			
		}
		for (int i = 0; i < lhsOfMemConsCombined.length() - 1; i++) {
			if (!idHasBeenAdded.get(i)) {
				int equalVarId = i;
				ArrayList<Integer> equalVarIdsGroup = new ArrayList<Integer> ();
				for (int j = i + 1; j < lhsOfMemConsCombined.length(); j++) {
					if (lhsOfMemConsCombined.charAt(equalVarId) == lhsOfMemConsCombined.charAt(j)) {
						equalVarIdsGroup.add(equalVarId);
						idHasBeenAdded.set(equalVarId, true);						
						equalVarId = j;
					}											
				}
				if (equalVarIdsGroup.size() > 0) {
					equalVarIdsGroup.add(equalVarId);
					equalVarIds.add(equalVarIdsGroup);
				}
			}
		}
		return equalVarIds;
	}
	
	public static String combinelhsOfMemCons(List<String> lhsOfMemCons) {
		String lhsOfMemConsCombined = "";
		for (String s: lhsOfMemCons) {
			lhsOfMemConsCombined = lhsOfMemConsCombined.concat(s);			
		}
		return lhsOfMemConsCombined;
	}
	
	
	/**
	 * @param simpleMembership 
	 * @return
	 */
	public static ArrayList<ArrayList<Automaton> > 
				  getsimpleMembershipDnf(Map<Integer, ArrayList<ArrayList<Automaton> > > simpleMembership) {
		ArrayList<ArrayList<Automaton> > result = simpleMembership.get(0);
		for (int i = 1; i < simpleMembership.keySet().size(); i++) {
			ArrayList<ArrayList<Automaton> > simpleMembershipDnf =
					conjunctionOfAutomataDnf2AutomataDnf(result, simpleMembership.get(i));
			result = simpleMembershipDnf;
		}
		return result;
	}
	
	public static HashMap<Integer, ArrayList<ArrayList<Automaton> > > 
	              getsimpleMembership(List<String> lhsOfMemCons, List<Automaton> rhsOfMemCons) {
		HashMap<Integer, ArrayList<ArrayList<Automaton> > > simpleMembership = 
				new HashMap<Integer, ArrayList<ArrayList<Automaton> > >();
		for (int i = 0; i < lhsOfMemCons.size(); i++) {
			int noOfVars = lhsOfMemCons.get(i).length();
			Automaton automaton = rhsOfMemCons.get(i);
			ArrayList<ArrayList<Automaton> > simpleDnf = new ArrayList<ArrayList<Automaton> > ();
			if (noOfVars > 1) { // the case for not simple membership 
				simpleDnf = membership2Simple(noOfVars, automaton);				
			}
			else { // the case for simple membership
				ArrayList<Automaton> simpleConjunctions = new ArrayList<Automaton> ();
				simpleConjunctions.add(automaton);
				simpleDnf.add(simpleConjunctions);
			}
			simpleMembership.put(i, simpleDnf);			
		}	
		return simpleMembership;
	}
	
	// precondition: noOfVars > 1
	public static ArrayList<ArrayList<Automaton> > membership2Simple(int noOfVars, Automaton automaton) {
		ArrayList<ArrayList<Automaton> > dnfOfSimple = new ArrayList<ArrayList<Automaton> > ();
		ArrayList<ArrayList<Integer> > permutations = getPermutations(automaton.getNumberOfStates(), noOfVars-1);
		List<State> stateList = new ArrayList<State> (); 
		int stateId = 0; 
		for (State s : automaton.getStates()) {
			stateList.add(stateId, s); 
			stateId++; 
		}
		int initialStateId = stateList.indexOf(automaton.getInitialState());
		dnfOfSimple = getAllAutomata(initialStateId, stateList, permutations, noOfVars-1);
		return dnfOfSimple;
	}

	public static ArrayList<ArrayList<Character> > getAutomataPermutations(ArrayList<ArrayList<Integer> > permutations, int permutationSize, List<Character>  states) {
		ArrayList<ArrayList<Character> > automataPermutations = new ArrayList<ArrayList<Character> >();
		for (int automataPermutationId = 0; automataPermutationId < permutations.size(); automataPermutationId++) {
			ArrayList<Character> automataPermutation = new ArrayList<Character>();
			ArrayList<Integer> permutation = permutations.get(automataPermutationId);
			for (int variableId = 0; variableId < permutationSize; variableId++) {
				automataPermutation.add(states.get(permutation.get(variableId)));								
			}
			System.out.println(automataPermutation.toString());
			automataPermutations.add(automataPermutation);			
		}
		return automataPermutations;
	}
	
	// getAllAutomata should be renamed to membershipToSimple
	public static ArrayList<ArrayList<Automaton> > getAllAutomata(int initialStateId, List<State> stateList, 
			                                        ArrayList<ArrayList<Integer> > permutations, int permutationSize) {
		ArrayList<ArrayList<Automaton> > allAutomata = new  ArrayList<ArrayList<Automaton> >(permutations.size());
		for (int permutationId = 0; permutationId < permutations.size(); permutationId++) {
			//System.out.println("Conjunction no " + permutationId + ": ");
			ArrayList<Integer> variablesAutomataAcceptStatesIds = permutations.get(permutationId);
			// we have (permutationSize+1) variables
			ArrayList<Automaton> conjunctionOfAutomata = new ArrayList<Automaton>(permutationSize + 1);
			int variableId = 0;
			// The start state of the first variable is the start state of the original automaton 
			// i.e = initialStateId
			int automatonInitialStateId = initialStateId;
			while (variableId < permutationSize) {
				int automatonAcceptStateId = variablesAutomataAcceptStatesIds.get(variableId);
				Automaton automaton = getAutomatonFromStates(automatonInitialStateId, automatonAcceptStateId, stateList, false);
				conjunctionOfAutomata.add(variableId, automaton);
				// the automaton of the next variable starts at the accept state of the previous
				// variable's automaton
				automatonInitialStateId = automatonAcceptStateId;
				//System.out.println("Variable no: " + variableId + " has automaton: " + automaton.toString());
				variableId++;				
			}
			// the automaton of the last variable has the accept state(s) of the original automaton 
			Automaton automaton = getAutomatonFromStates(automatonInitialStateId, -1, stateList, false);
			//System.out.println("Variable no: " + variableId + " has automaton: " + automaton.toString());
			conjunctionOfAutomata.add(variableId, automaton);
			// add the conjunction of the automata
			allAutomata.add(permutationId, conjunctionOfAutomata);
		}
		return allAutomata;
	}
	
	/**
	 * This method is used to construct an automaton with the same states and transitions 
	 * in stateList. However, the new constructed automaton can have a different initial state 
	 * and/or a different accept state. 
	 * @param initialStateId This is the id of the initial state of the returned automaton
	 * @param acceptStateId This is the id of the accept state of the returned automaton. It can
	 * be -1 if it is the same as the id of accept state(s) in statelist
	 * @param stateList This is the list of states to be used for constructing the automaton
	 * @return
	 */
	public static Automaton getAutomatonFromStates(int initialStateId, int acceptStateId,  List<State> stateList, boolean withOnlyOneSymbolTransitions) {
		Automaton newAutomaton = new Automaton();
		List<State> stateList2 = new ArrayList<State>(stateList.size());
		for (int i = 0; i < stateList.size(); i++) {
			State newState = new State();
			stateList2.add(i, newState);			
		}
		for (int i = 0; i < stateList2.size(); i++) {
			State oldState = stateList.get(i);
			State newState = stateList2.get(i);
			if (oldState.isAccept()) {
				newState.setAccept(true);				
			}
			Set<Transition> oldStateTransitions = oldState.getTransitions();
			if (withOnlyOneSymbolTransitions) {
				for (Transition oldTransition :  oldStateTransitions) {
					State oldStateNext = oldTransition.getDest();
					int oldStateNextId = stateList.indexOf(oldStateNext);
					char onlySingleSymbol = 'x';
					int newStateNextId = oldStateNextId;
					State newStateNext = stateList2.get(newStateNextId);
					Transition newTransition = new Transition(onlySingleSymbol, newStateNext);
					newState.addTransition(newTransition);								
				}
			}
			else {
				for (Transition oldTransition :  oldStateTransitions) {
					State oldStateNext = oldTransition.getDest();
					char t_min = oldTransition.getMin();
					char t_max = oldTransition.getMax();
					int oldStateNextId = stateList.indexOf(oldStateNext);
					int newStateNextId = oldStateNextId;
					State newStateNext = stateList2.get(newStateNextId);
					Transition newTransition = new Transition(t_min, t_max, newStateNext);
					newState.addTransition(newTransition);								
				}
			} 			
		}
		newAutomaton.setInitialState(stateList2.get(initialStateId));
		if (acceptStateId != -1) {
			// make all states as non-accepting states
			for (State s: stateList2) {
				s.setAccept(false);
			}
			//set the required state to be accepting one
			stateList2.get(acceptStateId).setAccept(true);
		}
		newAutomaton.restoreInvariant();
		newAutomaton.setDeterministic(true);
		return newAutomaton;
	}
	
	/**
	 * @param lasso This is input automaton in lasso form
	 * @return A dictionary of (k, v) pairs such that each pair represents 
	 * the conjunct (length(x) = k + v*i) where x is the string variable 
	 * recognized by lasso, i is a natural number
	 */
	public static Map<Integer, Integer> lassoAsLinearConstraint(Automaton lasso) {
		RunAutomaton runLasso = new RunAutomaton(lasso);
		Map<Integer, List<Integer> > stateToLength = new HashMap<Integer, List<Integer> >();
		Map<Integer, Integer> result = new HashMap<Integer, Integer> ();
		int startStateId = runLasso.getInitialState();
		//System.out.println("runLasso size:" + runLasso.getSize());
		State initialState = lasso.getInitialState();
		List<Transition> transitions =  initialState.getSortedTransitions(true);
		if (transitions.size() > 0) {
			char symbol = transitions.get(0).getMin();
			int currentStateId = startStateId;
			for (int stepCount = 0; stepCount < 2 * runLasso.getSize(); stepCount++) {
				if (runLasso.isAccept(currentStateId)) {
					if (stateToLength.containsKey(currentStateId)) {
						List<Integer> lengthConsPair = stateToLength.get(currentStateId);
						int m = lengthConsPair.get(0);
						int n = lengthConsPair.get(1);
						if (n == 0) {
							lengthConsPair.set(1, stepCount - m);
						}
					}
					else {
						List<Integer> lengthConsPair = new ArrayList<Integer> ();
						lengthConsPair.add(0, stepCount);
						lengthConsPair.add(1, 0);
						stateToLength.put(currentStateId, lengthConsPair);						
					}
				}
				currentStateId = runLasso.step(currentStateId, symbol);
				if (currentStateId == -1) {  // the case when there is no loop in lasso
					break;
				}
			}
			for (int key: stateToLength.keySet()) {
				List<Integer> lengthConsPair = stateToLength.get(key);
				int m = lengthConsPair.get(0);
				int n = lengthConsPair.get(1);
				result.put(m, n);
			}
		}
		else {
			if (initialState.isAccept()) {
				result.put(0, 0);				
			}
			else {                  // when there is only one state with a transition and is not accepting
				result.put(-1, 0);
			}
		}
		if (result.size() == 0) {   // when there are many states but none is accepting
			result.put(-1, 1);			
		}
		return result;
	}

	public static void testLassoAsLinearConstraint() {
		RegExp r = new RegExp("ab");
		Automaton a = r.toAutomaton();
		Automaton lasso = changeToOneSymbolAndMinimize(a);
		System.out.println("lasso has correct form: " + testLasso(lasso));
		System.out.println("lasso :" + lasso);
		System.out.println("lasso is deterministic : " + lasso.isDeterministic());
		Map<Integer, Integer> result = lassoAsLinearConstraint(lasso);
		System.out.println(result);
	}
	
	public static boolean testLasso(Automaton automaton) {
		boolean isLasso = true;
		for (State s: automaton.getStates()) {
			Set<Transition> transitions = s.getTransitions();
			if(transitions.size() > 1) {
				isLasso = false;
				break;
			}
		}
		return isLasso;
	}
	
	public static Automaton changeToOneSymbolAndMinimize(Automaton automaton) {
		List<State> stateList = new ArrayList<State>();
		int stateId = 0;
		for (State s : automaton.getStates()) { 
			  stateList.add(stateId, s); 
			  stateId++;
		}
		int initialStateId = stateList.indexOf(automaton.getInitialState()); 
		int acceptStateId = -1; // the accept state of the result is the same as the input's
		boolean withOnlyOneSymbolTransitions = true;
		Automaton result = 	getAutomatonFromStates(initialStateId, acceptStateId,  stateList, withOnlyOneSymbolTransitions);
		//System.out.println("getAutomatonFromStates : " + result);
		//System.out.println("getAutomatonFromStates is deterministic : " + result.isDeterministic());
		//result.setDeterministic(true);
		//System.out.println("Determinize getAutomatonFromStates: " + result);
		Automaton.setMinimization(Automaton.MINIMIZE_BRZOZOWSKI);
		result.minimize();
		result.restoreInvariant();
		//System.out.println(result);
		return result;
	}
	
	public static ArrayList<ArrayList<Integer> > getPermutations(int numOfStates, int size) {
		ArrayList<ArrayList<Integer> > permutations = new ArrayList<ArrayList<Integer> >();
		ArrayList<Integer> permutation = new ArrayList<Integer>();
		for (int i = 0; i < size; i++) {
			permutation.add(0);
		}
		int j = size - 1;
		while(true) {
			for(int i = 0; i < numOfStates; i++) {
				permutation.set(j, i);
				//System.out.println(permutation.toString());
				ArrayList<Integer> permutationCopy = new ArrayList<>(permutation);
				permutations.add(permutationCopy);
				//System.out.println(result.toString());
			}
			int k = j - 1;
			while(k >= 0 && permutation.get(k) == numOfStates -1) {
				permutation.set(k, 0);
				k = k - 1;
			}
			if (k >= 0) {
				int at_k = permutation.get(k);
				permutation.set(k, at_k + 1);				
			}
			else 
				break;
		}
		return permutations;
	}
	
	/**
	 * For each group of ids that represent the same variable, this method 
	 * makes the intersection of automata that have those ids.
	 * @param automataDisjunctions This is a disjunction of conjunctions of 
	 * automata where each disjunct ArrayList<Automaton> is a conjunction of automata 
	 * such that several automata might represent the same variable. 
	 * @param equalVarIds This is the list of groups where each group
	 * is a non-decreasing list of variable ids that represent the same variable. 
	 * @return The disjunction of conjunctions of automata where each 
	 * disjunct ArrayList<Automaton> is a conjunction of several automata and each 
	 * individual automaton represent a distinct variable
	 */
	public static ArrayList<ArrayList<Automaton> > intersectAutomata
				  (ArrayList<ArrayList<Automaton> > automataDisjunctions, 
				   ArrayList<ArrayList<Integer> > equalVarIds) {
		//System.out.println("in function intersectAutomata : automataDisjunctions size" + automataDisjunctions.size());
		ArrayList<ArrayList<Automaton> > result = new  ArrayList<ArrayList<Automaton> >();
		Map<Integer, Integer> similarIdMap = new HashMap<Integer, Integer>();
		for (int i = 0; i < equalVarIds.size(); i++) {
			// the group of ids representing the same variable
			ArrayList<Integer> similarIds = equalVarIds.get(i);
			// the least id of the variable that is represented by all subsequent ids in similarIds     
			int similarTo = similarIds.get(0);
			for (int j = 1; j < similarIds.size(); j++) {
				similarIdMap.put(similarIds.get(j), similarTo); 
			}			
		}
		//System.out.println(similarIdMap.toString());
		Set<Integer> similarIdMapValues = new HashSet<Integer>(similarIdMap.values()); 
		System.out.println("similarIdMapValues : " + similarIdMapValues.toString());
		ArrayList<Map<Integer, Automaton> > intersections = new ArrayList<Map<Integer, Automaton> >();
		for (int i = 0; i < automataDisjunctions.size(); i++) {
			//System.out.println("i : " + i);			
			Map<Integer, Automaton> int2Automaton = new HashMap<Integer, Automaton>();
			ArrayList<Automaton> automataConjunctions = automataDisjunctions.get(i);
			//System.out.println("automataConjunctions : " + automataConjunctions.toString());
			for (int id: similarIdMapValues) {
				Automaton automaton = automataConjunctions.get(id).clone();
				//System.out.println(automaton);
				int2Automaton.put(id, automaton);								
			}
			//System.out.println(int2Automaton.toString());
			for (int keyId: similarIdMap.keySet()) {
				int similarTo = similarIdMap.get(keyId); 
				Automaton automaton1 = int2Automaton.get(similarTo);
				Automaton automaton2 = automataConjunctions.get(keyId);
				Automaton automaton3 = automaton1.intersection(automaton2);
				int2Automaton.replace(similarTo, automaton3);					
			}
			intersections.add(i, int2Automaton);
		}
		for (int i = 0; i < intersections.size(); i++) {
			Map<Integer, Automaton> intersection = intersections.get(i);
			ArrayList<Automaton> automataConjunctions = automataDisjunctions.get(i);
			ArrayList<Automaton> newAutomataConjunctions = new ArrayList<Automaton> ();
			for (int j = 0; j < automataConjunctions.size(); j++) {
				if (!(similarIdMap.containsKey(j))) {
					if (intersection.containsKey(j)) {
						newAutomataConjunctions.add(intersection.get(j));						
					}
					else {
						newAutomataConjunctions.add(automataConjunctions.get(j));						
					}
				}
			}
			result.add(newAutomataConjunctions);
		}
		return result;
	}
	
	public static ArrayList<ArrayList<Automaton> > conjunctionOfAutomataDnf2AutomataDnf
									(ArrayList<ArrayList<Automaton> > automataDnf1,
									 ArrayList<ArrayList<Automaton> > automataDnf2) {
		ArrayList<ArrayList<Automaton> > result = new ArrayList<ArrayList<Automaton> > ();
		for (int i = 0; i < automataDnf1.size(); i++) {
			ArrayList<Automaton> conjunction1copy1 = getDeepCopy(automataDnf1.get(i));
			for (int j = 0; j < automataDnf2.size(); j++) {
				ArrayList<Automaton> conjunction1copy2 = getDeepCopy(conjunction1copy1);
				ArrayList<Automaton> conjunction2copy  = getDeepCopy(automataDnf2.get(j));
				ArrayList<Automaton> combinedConjunction = new ArrayList<Automaton> ();
				combinedConjunction.addAll(conjunction1copy2);
				combinedConjunction.addAll(conjunction2copy);	
				result.add(combinedConjunction);			
			}
		}
		return result;
	}

	public static ArrayList<Automaton> getDeepCopy(ArrayList<Automaton> automata) {
		ArrayList<Automaton> result = new ArrayList<Automaton> ();
		for (int i = 0; i < automata.size(); i++) {
			Automaton automatonCopy = automata.get(i).clone();
			result.add(automatonCopy);
		}
		return result;
	}
	
}