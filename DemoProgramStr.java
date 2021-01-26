import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
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
public class DemoProgramStr {

	public static void main(String[] args) {
		int noOfConjuncts = 1;
		ArrayList<ArrayList<String>> lhsOfMemCons_;
		List<Automaton> rhsOfMemCons;
		List<Map<String, Integer>> lhsOfLenCons_;
		List<Integer> rhsOfLenCons;
		List<IntegerRelation> relLhs2RhsOfLenCons;
		ArrayList<ArrayList<String>> lhsEqDeqCons_ ;
		ArrayList<ArrayList<String>> rhsEqDeqCons_ ;
		List<EqualityRelation> relLhs2RhsOfEqDeqCons;
		boolean satFound = false;
		int noOfExaminedConjuncts = 0;
		try {
            //opening file for reading in Java
            String file = "/home/hamid/eclipse-workspace/DemoProject/src/sat1.txt";
            BufferedReader reader = new BufferedReader(new FileReader(file));
            noOfConjuncts = getNumOfConjuncts(reader);
            System.out.println("Noofconj = " + noOfConjuncts);
            while (!satFound && (noOfExaminedConjuncts < noOfConjuncts)) {
            	lhsOfMemCons_ = new ArrayList<ArrayList<String>> () ;
        		rhsOfMemCons = new ArrayList<Automaton> ();
        		lhsOfLenCons_ = new ArrayList<Map<String, Integer>> ();
        		rhsOfLenCons = new ArrayList<Integer> ();
        		relLhs2RhsOfLenCons = new ArrayList<IntegerRelation> ();
        		lhsEqDeqCons_ = new ArrayList<ArrayList<String>> ();
        		rhsEqDeqCons_ = new ArrayList<ArrayList<String>> ();
        		relLhs2RhsOfEqDeqCons = new ArrayList<EqualityRelation> ();
            	getMemConstraints(reader, lhsOfMemCons_, rhsOfMemCons);
                getLengthConstraints_(reader, lhsOfLenCons_, relLhs2RhsOfLenCons, rhsOfLenCons);
                getEqDeqConstraints_(reader, lhsEqDeqCons_, relLhs2RhsOfEqDeqCons, rhsEqDeqCons_);
                System.out.println("lhsOfMemCons = " + lhsOfMemCons_);
                System.out.println("lhsOfLenCons_ = " + lhsOfLenCons_);
                System.out.println("lhsEqDeqCons_ = " + lhsEqDeqCons_);
                satFound = runSolver(lhsOfMemCons_, rhsOfMemCons, 
                		             lhsOfLenCons_, relLhs2RhsOfLenCons, rhsOfLenCons,
                		             lhsEqDeqCons_, relLhs2RhsOfEqDeqCons, rhsEqDeqCons_);
                noOfExaminedConjuncts = noOfExaminedConjuncts + 1;                
            }
            reader.close();
                 
        } catch (FileNotFoundException ex) {
            System.out.println("File not found");
        } catch (IOException ex) {
        	System.out.println("IO exception");
        }
	}
		
		
	private static boolean runSolver(ArrayList<ArrayList<String>> lhsOfMemCons_, List<Automaton> rhsOfMemCons, 
			                         List<Map<String, Integer>> lhsOfLenCons_, List<IntegerRelation> relLhs2RhsOfLenCons, List<Integer> rhsOfLenCons, 
			                         ArrayList<ArrayList<String>> lhsEqDeqCons_, List<EqualityRelation> relLhs2RhsOfEqDeqCons, ArrayList<ArrayList<String>> rhsEqDeqCons_) {	
		/***********************************************************************************/
		boolean result = false;
		ArrayList<ArrayList<Map<Integer, Integer> > > refinedIntegerArithDnf_ =
				new ArrayList<ArrayList<Map<Integer, Integer> > > ();
		ArrayList<String> variables_ = new ArrayList<String> ();
		processMembershipConstraints_(variables_, refinedIntegerArithDnf_, lhsOfMemCons_, rhsOfMemCons);
		//System.out.println("variables_: " + variables_);
		//System.out.println("refinedIntegerArithDnf_: " + refinedIntegerArithDnf_);
		if(refinedIntegerArithDnf_.size() == 0) {
			//System.out.println("memebership constraints are UNSAT");
		}
		else {		
			final Context context = new Context();
			final Solver solver = context.mkSimpleSolver();
			Map<String, IntExpr> lengthVariables_ = makeLengthVariables_(context, variables_);
			System.out.println("lengthVariables_ = " + lengthVariables_);
			addLengthConstraintsToSolver_(lhsOfLenCons_, relLhs2RhsOfLenCons, rhsOfLenCons, 
					                     lengthVariables_, context, solver);
			//System.out.println("solver after adding length constraints= " + solver.toString());
			//Status st = solver.check();
			// if length constraints alone are satisfiable, we check the membership constraints
			if (solver.check().equals(Status.SATISFIABLE)) {
				System.out.println("Length constraints are SATISFIABLE");
				// the remaining code should go in here
				int previousSatIntegerArithDisjId = -1;
				//solver.push();
				int nextSatIntegerArithDisjId_;
				boolean stopFlag = false;
				boolean solution_found = false;
				while (!stopFlag) {
					int temp_count = 1 + previousSatIntegerArithDisjId + refinedIntegerArithDnf_.size();
					System.out.println("#remaining over-approx solutions= " + temp_count);
					// if we already pushed a disjunct of membership constraints, we need to pop 
					// them before we push the next disjunct
					if (previousSatIntegerArithDisjId > -1) {
						solver.pop();
					}
					nextSatIntegerArithDisjId_ = getNextSatIntegerArithDisjId_(refinedIntegerArithDnf_, 
		                    lengthVariables_, variables_, context, solver, 
		                    previousSatIntegerArithDisjId);
					if (previousSatIntegerArithDisjId < refinedIntegerArithDnf_.size()) {
						//System.out.println("nextSatIntegerArithDisjId_ = " + nextSatIntegerArithDisjId_);
						while (solver.check().equals(Status.SATISFIABLE)) {
							//System.out.println("solver after adding membership constraints= " + solver.toString());						
							Model model = solver.getModel();
							//System.out.println(model.toString());
							String maxLenVar = getMaxLenVar(
									lengthVariables_, model);
							Expr maxLenVar_expr = model.getConstInterp(lengthVariables_.get(maxLenVar));
							String maxLenVar_str = maxLenVar_expr.toString();	
							int maxLenVar_int = Integer.parseInt(maxLenVar_str);
							//System.out.println("max len var is " + maxLenVar + " with length of " + maxLenVar_int);
							solution_found = underApproximation_(variables_, 
						            lhsEqDeqCons_, 
						            relLhs2RhsOfEqDeqCons, 
						            rhsEqDeqCons_,
						            lhsOfMemCons_, 
						            rhsOfMemCons,
						            lhsOfLenCons_, 
						            relLhs2RhsOfLenCons, 
						            rhsOfLenCons,
						            lengthVariables_,
						            maxLenVar_int,
						            context,
						            solver);
							if (solution_found) {
								stopFlag = true;
								result = true;
								break;							
							}
							else {

								BoolExpr underApproxConstraint = context.mkBool(false);
								for (String k: lengthVariables_.keySet()) {
									IntExpr k_var = lengthVariables_.get(k);
									BoolExpr under_temp = context.mkGt(k_var, (IntExpr)maxLenVar_expr);
									underApproxConstraint = context.mkOr(underApproxConstraint, under_temp);
								}
								solver.add(underApproxConstraint);
							}														
						}	
					}
					else {
						stopFlag = true;
					}					
					previousSatIntegerArithDisjId = nextSatIntegerArithDisjId_;					
				}
				
			}
			
		}
		return result;
	}
	
	private static int getNumOfConjuncts(BufferedReader reader) {
		// TODO Auto-generated method stub
		int result = 0;
		try {
			String line;
			line = reader.readLine();
	        String[] lineArray = line.split(":");
	        
	        result = Integer.parseInt(lineArray[1]);
			
		} catch (FileNotFoundException ex) {
			System.out.println("File not found");
        } 
		catch (IOException ex) {
			System.out.println("IO exception");
    	}
		
		return result;
	}
	
	private static void getMemConstraints(BufferedReader reader, ArrayList<ArrayList<String>> lhsOfMemCons,
			List<Automaton> rhsOfMemCons) {		
		try {
			String line;
	        line = reader.readLine();
	        String[] lineArray = line.split(":");
	        System.out.println(Arrays.toString(lineArray));
	        //System.out.println("lineArray[0] " + lineArray[0]);
	        //String membConsName = "#membership_constraints";
	        int noOfmembCons = Integer.parseInt(lineArray[1]);
	        System.out.println(noOfmembCons);
	        int noOfConsRead = 0;
	        while(noOfConsRead < noOfmembCons){
	        	ArrayList<String> lhsOfMemConsI = new ArrayList<String>();
	        	line = reader.readLine();
	        	//System.out.println(line);
	        	String[] data = line.split("\t");
		        //System.out.println(Arrays.toString(data));
		        String lhsOfMemConsStr = data[0];
		        //System.out.println("lhsOfMemConsStr " + lhsOfMemConsStr);
		        for (int i = 0; i < lhsOfMemConsStr.length(); i++) {
		        	lhsOfMemConsI.add(Character.toString(lhsOfMemConsStr.charAt(i)));		        			        	
		        }
		        //System.out.println("lhsOfMemConsI " + lhsOfMemConsI);
		        lhsOfMemCons.add(lhsOfMemConsI);
		        System.out.println("rhsOfMemConsI " + data[1]);
		        RegExp rhsOfMemConsRegexI;
		        Automaton rhsOfMemConsI;
		        if (data[1].charAt(data[1].length()-1) == '\'') {
		        	String rhsModified = data[1].substring(0, data[1].length()-1);
		        	rhsOfMemConsRegexI = new RegExp(rhsModified);	
		        	System.out.println("rhsModified " + rhsModified);
		        	rhsOfMemConsI = rhsOfMemConsRegexI.toAutomaton().complement();
		        }
		        else {
		        	rhsOfMemConsRegexI = new RegExp(data[1]);		        	
		        	rhsOfMemConsI = rhsOfMemConsRegexI.toAutomaton();
		        }
		        	
		        //System.out.println("rhsOfMemConsRegexIStr " + data[1]);
		        //System.out.println("rhsOfMemConsRegexI " + rhsOfMemConsRegexI);
		        //Automaton rhsOfMemConsI = rhsOfMemConsRegexI.toAutomaton();
		        //System.out.println("rhsOfMemConsI " + rhsOfMemConsI);
		        rhsOfMemCons.add(rhsOfMemConsI);
		        noOfConsRead++;	        	
	        }
	        //System.out.println("lhsOfMemCons " + lhsOfMemCons);
	        //System.out.println("rhsOfMemCons " + rhsOfMemCons);
        } 
		catch (FileNotFoundException ex) {
			System.out.println("File not found");
        } 
		catch (IOException ex) {
			System.out.println("IO exception");
    	}
	}
	
	private static void getLengthConstraints_(BufferedReader reader, List<Map<String, Integer>> lhsOfLenCons_,
			List<IntegerRelation> relLhs2RhsOfLenCons, List<Integer> rhsOfLenCons) {
		// TODO Auto-generated method stub
		try {
			String line;
			line = reader.readLine();
	        String[] lineArray = line.split(":");
	        //System.out.println(Arrays.toString(lineArray));
	        String lenConsName = "#length_constraints";
            int noOfLenCons = Integer.parseInt(lineArray[1]);
            //System.out.println(noOfLenCons);
            int noOfConsRead = 0;
	        //System.out.println("lhsOfMemCons " + lhsOfMemCons);
	        //System.out.println("rhsOfMemCons " + rhsOfMemCons);
            while(noOfConsRead < noOfLenCons){
            	line = reader.readLine();
	        	//System.out.println(line);
		        String[] data = line.split("\t");
		        IntegerRelation relLhs2RhsOfLenConsI = IntegerRelation.NOTEQUAL;
		        String relLhs2RhsOfLenConsStr = data[0];
		        if (relLhs2RhsOfLenConsStr.equals(">"))
		        	relLhs2RhsOfLenConsI = IntegerRelation.GREATER;
		        else if (relLhs2RhsOfLenConsStr.equals(">="))
		        	relLhs2RhsOfLenConsI = IntegerRelation.GREATEREQUAL;
		        else if (relLhs2RhsOfLenConsStr.equals("<"))
		        	relLhs2RhsOfLenConsI = IntegerRelation.LESS;
		        else if (relLhs2RhsOfLenConsStr.equals("<="))
		        	relLhs2RhsOfLenConsI = IntegerRelation.LESSEQUAL;
		        else
		        	relLhs2RhsOfLenConsI = IntegerRelation.EQUAL;
		        
		        Map<String, Integer> lhsOfLenConsI = new HashMap<String, Integer> ();
		        for (int termId = 1; termId < data.length - 1; termId++) {
		        	String leftTermWithP = data[termId];
		        	String leftTerm = leftTermWithP.substring(1, leftTermWithP.length()-1);
		        	//System.out.println(leftTerm);
		        	String[] termContents = leftTerm.split(" ");
		            //System.out.println(Arrays.toString(termContents));
		            String termSign = termContents[0];
		            int termCoeff = Integer.parseInt(termContents[1]);
		            if (termSign.equals("-"))
		            	termCoeff = 0 - termCoeff;
		            lhsOfLenConsI.put(termContents[2], termCoeff);
		        }
		        int rhsOfLenConsI = Integer.parseInt(data[data.length - 1]);
		        //System.out.println(rhsOfLenConsI);
		        lhsOfLenCons_.add(lhsOfLenConsI);
		        relLhs2RhsOfLenCons.add(relLhs2RhsOfLenConsI);
		        rhsOfLenCons.add(rhsOfLenConsI);
		        
		        //System.out.println(Arrays.toString(data));
		        noOfConsRead++;
	        }
        }
		catch (FileNotFoundException ex) {
			System.out.println("File not found");
        } 
		catch (IOException ex) {
			System.out.println("IO exception");
    	}
	}
	
	private static void getEqDeqConstraints_(BufferedReader reader, ArrayList<ArrayList<String>> lhsEqDeqCons_,
			List<EqualityRelation> relLhs2RhsOfEqDeqCons, ArrayList<ArrayList<String>> rhsEqDeqCons_) {
		// TODO Auto-generated method stub
		try {
			String line;
			line = reader.readLine();
	        String[] lineArray = line.split(":");
	        
	        String eqConsName = "#equality_constraints";
            int noOfEqCons = Integer.parseInt(lineArray[1]);
            
            int noOfConsRead = 0;
	        
            while(noOfConsRead < noOfEqCons){
            	line = reader.readLine();
	        	
		        String[] data = line.split("\t");
		        EqualityRelation relLhs2RhsOfEqDeqConsI = EqualityRelation.EQUAL;
		        String relLhs2RhsOfEqDeqConsStr = data[0];
		        if (relLhs2RhsOfEqDeqConsStr.equals("!="))
		        	relLhs2RhsOfEqDeqConsI = EqualityRelation.NOTEQUAL;
		        
		        ArrayList<String> lhsEqDeqConsI = new ArrayList<String> ();
		        ArrayList<String> rhsEqDeqConsI = new ArrayList<String> ();
		        
		        String leftTerm = data[1];
		        
		        String[] leftTermContents = leftTerm.split("\\.");
		        
		        for (int i = 0; i < leftTermContents.length; i++) {
		        	lhsEqDeqConsI.add(leftTermContents[i]);		        	
		        }
		        
		        lhsEqDeqCons_.add(lhsEqDeqConsI);
		        
		        String rightTerm = data[2];
		        
		        String[] rightTermContents = rightTerm.split("\\.");
		        
		        for (int i = 0; i < rightTermContents.length; i++) {
		        	rhsEqDeqConsI.add(rightTermContents[i]);		        	
		        }
		        
		        rhsEqDeqCons_.add(rhsEqDeqConsI);
		        		        
		        noOfConsRead++;
	        }
        }
		catch (FileNotFoundException ex) {
			System.out.println("File not found");
        } 
		catch (IOException ex) {
			System.out.println("IO exception");
    	}

		
	}


	private static String getMaxLenVar(Map<String, IntExpr> lengthVariables, Model model) {
		// TODO Auto-generated method stub
		String result = "";
		int max_len = -1;
		for (String var:lengthVariables.keySet()) {
			Expr var_expr = model.getConstInterp(lengthVariables.get(var));
			String var_str = var_expr.toString();	
			int var_int = Integer.parseInt(var_str);
			if (var_int > max_len) {
				max_len = var_int;
				result = var;
			}
		}
		//System.out.println("max len var is " + result + " with length of " + max_len);
		return result;
	}

	private static boolean underApproximation_(ArrayList<String> u_variables_, ArrayList<ArrayList<String>> lhsEqDeqCons_,
			List<EqualityRelation> relLhs2RhsOfEqDeqCons, ArrayList<ArrayList<String>> rhsEqDeqCons_, ArrayList<ArrayList<String>> lhsOfMemCons_, List<Automaton> rhsOfMemCons, List<Map<String, Integer>> lhsOfLenCons_, List<IntegerRelation> relLhs2RhsOfLenCons, List<Integer> rhsOfLenCons, Map<String, IntExpr> oldLengthVariables, int maxLenVar_int, Context context, Solver solver) {
		// TODO Auto-generated method stub
		//System.out.println("****************************************************************");
		//System.out.println("****************************************************************");
		//System.out.println("The UnderApproximation function");
		//System.out.println("The lhsEqDeqCons: " + lhsEqDeqCons_);
		//System.out.println("The relLhs2RhsOfEqDeqCons: " + relLhs2RhsOfEqDeqCons);
		//System.out.println("The rhsEqDeqCons: " + rhsEqDeqCons_);
		// u_variables should be substituted with variable. it is used here for testing the
		// underApproximation function implementation
		//ArrayList<String> u_variables = new ArrayList<String> ();
		// u_variables[i] is split into a number of variables. This number is u_variables_split_count[i]
		ArrayList<Integer> u_variables_split_count = new ArrayList<Integer> ();
		Map<String, ArrayList<String> > u_variables_split = new HashMap<String, ArrayList<String> > ();
		Map<String, ArrayList<String> > u_variables_split2 = new HashMap<String, ArrayList<String> > ();
		//ArrayList<String> extended_variables = new ArrayList<String> ();
		ArrayList<String> extended_variables;
		//System.out.println("u_variables: " + u_variables_);
		//int K_parameter = 3;
		boolean solution_found = false;
		ArrayList<ArrayList<Integer>> lengthPermutations = 
				getPermutations2(maxLenVar_int, u_variables_.size());
		//System.out.println("lengthPermutations: " + lengthPermutations);
		//u_variables_split_count = lengthPermutations.get(7);
		for (int uid = 0; uid < lengthPermutations.size(); uid++) {
			//System.out.print("under-approximation is checking solution no. " + uid);	
			//System.out.println("out of the " + lengthPermutations.size() + " alternatives");
			extended_variables = new ArrayList<String> ();
			u_variables_split_count = lengthPermutations.get(uid);
			//System.out.println("u_variables_split_count: " + u_variables_split_count);
			for (int i = 0; i < u_variables_.size(); i++) {
				String c = u_variables_.get(i);
				int split_count = u_variables_split_count.get(i);
				ArrayList<String> c_split_into = new ArrayList<String> ();
				for (int j = 1; j <= split_count; j++) {
					c_split_into.add(c + j);				
				}
				extended_variables.addAll(c_split_into);
				u_variables_split.put(c, c_split_into);
			}
			//System.out.println("u_variables_split: " + u_variables_split);
			//System.out.println("extended_variables: " + extended_variables);
			// fixedVars should contain the value(s) for each variable,
			// for example fixedVars[x1] = {y2,z3} means that x1 = y2 and x1 = z3
			// fixedVars[x] = {.., x, ..} is not allowed
			Map<String, HashSet<String> > fixedVars = new HashMap<String, HashSet<String> > ();
			for (String c: u_variables_) {
				for (String s: u_variables_split.get(c) ) {
					HashSet<String> s_values = new HashSet<String> ();
					fixedVars.put(s, s_values);					
				}		
			}
			
			//System.out.println("fixedVars: " + fixedVars);
			//System.out.println("fixedVars size: " + fixedVars.size());
			for (int id = 0; id < lhsEqDeqCons_.size(); id++) {
				// each variable is expressed by its split variables,
				// i.e x = u_variables[i] is written as u_variables_split[x]
				ArrayList<String> splitLhsEqDeqConsI = new ArrayList<String> ();
				ArrayList<String> splitRhsEqDeqConsI = new ArrayList<String> ();
				ArrayList<String> lhsEqDeqConsI = lhsEqDeqCons_.get(id);
				ArrayList<String> rhsEqDeqConsI = rhsEqDeqCons_.get(id);
				for (int i = 0; i < lhsEqDeqConsI.size(); i++) {
					String c = lhsEqDeqConsI.get(i);
					ArrayList<String> c_split = u_variables_split.get(c);
					for (int j = 0; j < c_split.size(); j++) {
						splitLhsEqDeqConsI.add(c_split.get(j));				
					}
				}
				for (int i = 0; i < rhsEqDeqConsI.size(); i++) {
					String c = rhsEqDeqConsI.get(i);
					ArrayList<String> c_split = u_variables_split.get(c);
					for (int j = 0; j < c_split.size(); j++) {
						splitRhsEqDeqConsI.add(c_split.get(j));				
					}
				}
				//System.out.println("splitLhsEqDeqConsI: " + splitLhsEqDeqConsI);
				//System.out.println("splitRhsEqDeqConsI: " + splitRhsEqDeqConsI);
				fixVariables(fixedVars, splitLhsEqDeqConsI, splitRhsEqDeqConsI);	
			}
			//System.out.println("fixedVars: " + fixedVars);
			preprocessVars(fixedVars, u_variables_split, u_variables_split2);
			//System.out.println("fixedVars: " + fixedVars);
			//System.out.println("u_variables_split: " + u_variables_split);
			//System.out.println("u_variables_split2: " + u_variables_split2);
			
			//System.out.println("Permutations: " + getPermutations(2,2));
			// In newLhsOfMemCons, variables are substituted according to u_variables_split
			ArrayList<ArrayList<String>> newLhsOfMemCons = new ArrayList<ArrayList<String>> ();
			getNewLhsOfMemCons(newLhsOfMemCons, lhsOfMemCons_, u_variables_split2);
			//System.out.println("lhsOfMemCons_: " + lhsOfMemCons_);
			//System.out.println("newLhsOfMemCons: " + newLhsOfMemCons);
			// ArrayList<ArrayList<String>> lhsOfLenCons_, List<IntegerRelation> relLhs2RhsOfLenCons, List<Integer> rhsOfLenCons
			List<Map<String, Integer>>  newlhsOfLenCons = new ArrayList<Map<String, Integer>> ();
			getNewLhsOfLenCons(newlhsOfLenCons, lhsOfLenCons_, u_variables_split2);
			//System.out.println("lhsOfLenCons_: " + lhsOfLenCons_);
			//System.out.println("newlhsOfLenCons: " + newlhsOfLenCons);
			Map<String, IntExpr> newLengthVariables = makeLengthVariables_(context, extended_variables);
			//System.out.println("newLengthVariables: " + newLengthVariables);
			solver.push();
			addLengthConstraintsToSolver_(newlhsOfLenCons, relLhs2RhsOfLenCons, rhsOfLenCons, 
					newLengthVariables, context, solver);
			addSplitVariablesToSolver(oldLengthVariables, newLengthVariables, u_variables_split, u_variables_split2, context, solver);
			solution_found = addMemConstraintsToSolver_(newLhsOfMemCons, rhsOfMemCons, newLengthVariables, context, solver);

			// no need foraddfixedVariablesToSolver
			//addfixedVariablesToSolver(fixedVars, newLengthVariables, context, solver);
			//System.out.println("solver = " + solver.toString());
			if (solution_found) {
//			if (solver.check().equals(Status.SATISFIABLE)) {
//				solution_found = true;
//				System.out.println("The under-approximation found a solution for length constraints");
//				System.out.println("in the " + (uid + 1) + " / " + lengthPermutations.size() + " attempt.");
//				Model model = solver.getModel();
//				System.out.println(model.toString());
//				solution_found = addMemConstraintsToSolver_(newLhsOfMemCons, rhsOfMemCons, newLengthVariables, context, solver);
				//solver.pop();
				break;					
			}
			else {
				solver.pop();				
			}
		}
		if (!solution_found) {
			//System.out.print("under-approximation has not found a solution");	
			//System.out.println("out of the " + lengthPermutations.size() + " alternatives");	
		}
		return solution_found;
	}

	private static boolean addMemConstraintsToSolver_(ArrayList<ArrayList<String>> newLhsOfMemCons,
			List<Automaton> rhsOfMemCons, Map<String, IntExpr> newLengthVariables, Context context, Solver solver) {
		// TODO Auto-generated method stub
		boolean result = false;
		//System.out.println("addMemConstraintsToSolver_Start");
		//System.out.println("newLhsOfMemCons " + newLhsOfMemCons);
		//System.out.println("newLengthVariables " + newLengthVariables);
		int count_new_var = 0;
		ArrayList<ArrayList<String>> processedLhsOfMemCons = new ArrayList<ArrayList<String>> ();
		List<Automaton> processedRhsOfMemCons =  new ArrayList<Automaton> ();
		for (int i = 0; i < rhsOfMemCons.size(); i++) {
			ArrayList<String> LhsOfMemConsI = newLhsOfMemCons.get(i);
			Automaton automataI = rhsOfMemCons.get(i);
			if (LhsOfMemConsI.size() > 0) {
				processedLhsOfMemCons.add(LhsOfMemConsI);
				processedRhsOfMemCons.add(automataI);
			}
			else {
				if (!(automataI.run("")))
					return false;				
//				count_new_var++;
//				String c = "fresh_var" + String.valueOf(count_new_var);
//				IntExpr fresh_var = context.mkIntConst("len_" + c);
//				newLengthVariables.put(c, fresh_var);
//				ArrayList<String> newLhsOfMemConsI = new ArrayList<String> ();
//				newLhsOfMemConsI.add(c);
//				processedLhsOfMemCons.add(newLhsOfMemConsI);
//				// add that |fresh_var| = 0
//				BoolExpr emptyVar = context.mkEq(newLengthVariables.get(c), context.mkInt(0));
//				solver.add(emptyVar);
			}
		}
		if (processedLhsOfMemCons.size() == 0) {
			System.out.println("The under-approximation found a solution");
			Model model = solver.getModel();
			System.out.println(model.toString());
			return true;
			
		}
		//System.out.println("processedLhsOfMemCons " + processedLhsOfMemCons);
//		if (processedLhsOfMemCons.size() == 0) { // no membership constraints to test
//			System.out.println("The under-approximation found a solution");
//			Model model = solver.getModel();
//			System.out.println(model.toString());
//			return true;
//		}
		ArrayList<ArrayList<Map<Integer, Integer> > > newRefinedIntegerArithDnf_ =
				new ArrayList<ArrayList<Map<Integer, Integer> > > ();
		ArrayList<String> newVariables_ = new ArrayList<String> ();
		processMembershipConstraints_(newVariables_, newRefinedIntegerArithDnf_, processedLhsOfMemCons, processedRhsOfMemCons);
		//System.out.println("newRefinedIntegerArithDnf_ " + newRefinedIntegerArithDnf_);
		if(newRefinedIntegerArithDnf_.size() == 0) {
			//System.out.println("memebership constraints are UNSAT");
			//return result;
		}
		else {
			for (int i = 0; i < newRefinedIntegerArithDnf_.size(); i++) {
				ArrayList<Map<Integer, Integer>> nextIntegerArithDisj = 
						newRefinedIntegerArithDnf_.get(i);
				solver.push();
				boolean isSat_ = testSat_(nextIntegerArithDisj, newLengthVariables, newVariables_, context, solver);
				if (isSat_) {
					System.out.println("The under-approximation found a solution");
					Model model = solver.getModel();
					System.out.println(model.toString());
					result = true;
					break;
					//return result;
				}
				else {
					solver.pop();
				}				
			}
		}
		//System.out.println("addMemConstraintsToSolver_End");
		return result; 		
	}


	private static void preprocessVars(Map<String, HashSet<String>> fixedVars, Map<String, ArrayList<String>> u_variables_split1, Map<String, ArrayList<String>> u_variables_split2) {
		// TODO Auto-generated method stub
		int count = 0;
		Map<String, Integer> equalVarsMap = new HashMap<String, Integer> ();
		for(String key: fixedVars.keySet()) {
			HashSet<String> values = fixedVars.get(key);
			if (equalVarsMap.keySet().contains(key)) {
				int val = equalVarsMap.get(key);
				for (String v: values) {
					equalVarsMap.put(v, val);					
				}
			}
			else {
				boolean b = false;
				int val = 0;
				for (String v: values) {
					if (equalVarsMap.keySet().contains(v)) {
						val = equalVarsMap.get(v);
						b = true;
						break;
					}					
				}
				if (b) {
					equalVarsMap.put(key, val);
					for (String v: values) {
						equalVarsMap.put(v, val);						
					}
				}
				else {
					count = count + 1;
					equalVarsMap.put(key, count);
					for (String v: values) {
						equalVarsMap.put(v, count);						
					}
				}
			}
		} 
		Map<Integer, TreeSet<String>> equalVarsClusters = new HashMap<Integer, TreeSet<String>> ();
		for (String s: equalVarsMap.keySet()) {
			int groupId = equalVarsMap.get(s);
			if (equalVarsClusters.containsKey(groupId)) {
				equalVarsClusters.get(groupId).add(s);
			}
			else {
				TreeSet<String> equalVarsSet = new TreeSet<String> ();
				equalVarsSet.add(s);
				equalVarsClusters.put(groupId, equalVarsSet);
			}
		}
		//System.out.println("equalVarsMap = " + equalVarsMap);
		//System.out.println("equalVarsClusters = " + equalVarsClusters);
		Map<Integer, String> equalVarsMap2 = new HashMap<Integer, String> ();
		for (Integer key: equalVarsClusters.keySet()) {
			TreeSet<String> equalVarsSet = equalVarsClusters.get(key);
			if (equalVarsSet.contains("EPSILON")) {
				equalVarsMap2.put(key, "EPSILON");								
			}
			else {
				equalVarsMap2.put(key, equalVarsSet.last());								
			}
		}
		//System.out.println("equalVarsMap2 = " + equalVarsMap2);
		//System.out.println("u_variables_split1 = " + u_variables_split1);
		for (String s: u_variables_split1.keySet()) {
			ArrayList<String> s_split_into1 = u_variables_split1.get(s);
			ArrayList<String> s_split_into2 = new ArrayList<String> ();
			if (s_split_into1.size() == 0) {
				u_variables_split2.put(s, s_split_into2);				
			}
			else {
				for (int i = 0; i < s_split_into1.size(); i++) {
					String v1 = s_split_into1.get(i);
					if (equalVarsMap.containsKey(v1)) {
						String v2 = equalVarsMap2.get(equalVarsMap.get(v1));
						if (!v2.equals("EPSILON")) {
							s_split_into2.add(v2);						
						}
					}
					else {
						s_split_into2.add(v1);					
					}
					u_variables_split2.put(s, s_split_into2);
				}
			}
		}
		//System.out.println("u_variables_split2 = " + u_variables_split2);		
	}

	private static void addSplitVariablesToSolver(Map<String, IntExpr> oldLengthVariables,
			Map<String, IntExpr> newLengthVariables, Map<String, ArrayList<String>> variables_split1, Map<String, ArrayList<String>> variables_split2, Context context, Solver solver) {
		// TODO Auto-generated method stub
		//System.out.println("oldLengthVariables = " + oldLengthVariables);
		//System.out.println("newLengthVariables = " + newLengthVariables);
		//System.out.println("variables_split1 = " + variables_split1);
		//System.out.println("variables_split2 = " + variables_split2);
		for (String leftVar: variables_split1.keySet()) {
			IntExpr oldVar = oldLengthVariables.get(leftVar);
			IntExpr extendedVar = context.mkInt(0);			
			for (String rightVar: variables_split1.get(leftVar)) {
				extendedVar = (IntExpr) context.mkAdd(newLengthVariables.get(rightVar), extendedVar);												
			}
			BoolExpr b = context.mkEq(oldVar, extendedVar);
			//System.out.println("b = " + b);
			solver.add(b);
		}
		for (String leftVar: variables_split2.keySet()) {
			IntExpr oldVar = oldLengthVariables.get(leftVar);
			IntExpr extendedVar = context.mkInt(0);			
			for (String rightVar: variables_split2.get(leftVar)) {
				extendedVar = (IntExpr) context.mkAdd(newLengthVariables.get(rightVar), extendedVar);												
			}
			BoolExpr b = context.mkEq(oldVar, extendedVar);
			//System.out.println("b = " + b);
			solver.add(b);
		}
	}

	private static void getNewLhsOfLenCons(List<Map<String, Integer>> newLhsOfLenCons,
			List<Map<String, Integer>> oldLhsOfLenCons, Map<String, ArrayList<String>> variables_split) {
		// TODO Auto-generated method stub
		for (int i = 0; i < oldLhsOfLenCons.size(); i++) {
			Map<String, Integer> oldLenCons = oldLhsOfLenCons.get(i);
			Map<String, Integer> newLenCons = new HashMap<String, Integer> ();
			for (String strVar: oldLenCons.keySet()) {
				int varLength = oldLenCons.get(strVar);
				for (String s: variables_split.get(strVar)) {
					newLenCons.put(s, varLength);																									
				}
			}
			newLhsOfLenCons.add(newLenCons);
		}
	}

	private static void getNewLhsOfMemCons(ArrayList<ArrayList<String>> newLhsOfMemCons,
			ArrayList<ArrayList<String>> oldLhsOfMemCons, Map<String, ArrayList<String>> variables_split) {
		// TODO Auto-generated method stub
		for (int i = 0; i < oldLhsOfMemCons.size(); i++) {
			ArrayList<String> oldLhsCons = oldLhsOfMemCons.get(i);
			ArrayList<String> newLhsCons = new ArrayList<String> ();
			for (int j = 0; j < oldLhsCons.size(); j++) {
				//System.out.println("test1: " + oldLhsCons.get(j));
				//System.out.println("test2: " + variables_split.get(oldLhsCons.get(j)));
				newLhsCons.addAll(variables_split.get(oldLhsCons.get(j)));				
			}
			newLhsOfMemCons.add(newLhsCons);
		}
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

	private static int getNextSatIntegerArithDisjId_(
			ArrayList<ArrayList<Map<Integer, Integer>>> refinedIntegerArithDnf_, Map<String, IntExpr> lengthVariables_,
			ArrayList<String> variables_, Context context, Solver solver, int previousSatIntegerArithDisjId) {
		// TODO Auto-generated method stub
		// the previous IntegerArithDisj didn't result in SAT constraints, so 
		// have to examine the next IntegerArithDisj
		int nextIntegerArithDisjId = previousSatIntegerArithDisjId + 1;
		while(nextIntegerArithDisjId < refinedIntegerArithDnf_.size()) {	 
			ArrayList<Map<Integer, Integer>> nextIntegerArithDisj = 
					refinedIntegerArithDnf_.get(nextIntegerArithDisjId);
			solver.push();
			boolean isSat_ = testSat_(nextIntegerArithDisj, lengthVariables_, variables_, context, solver);
			System.out.println("isSat = " + isSat_);
			if (isSat_) {
				return nextIntegerArithDisjId;				
			}
			else {
				solver.pop();
				nextIntegerArithDisjId = nextIntegerArithDisjId + 1;
			}
		}
		return nextIntegerArithDisjId;
	}

	private static boolean testSat_(ArrayList<Map<Integer, Integer>> lassoList,
			Map<String, IntExpr> lengthVariables_, ArrayList<String> variables_, Context ctx, Solver solver) {
		// TODO Auto-generated method stub
		// ArrayList<ArrayList<Map<Integer, Integer> > > integerArithDnf 
		// [{0=0}, {0=2, 1=1, 2=1}, {1=3}, {1=0, 2=2}]
		// this represents the following:
		// (len(var0) = 0) and (len(var1) = 2i or len(var1) = 1 + i or len(var1) = 2 + i) and
		// (len(var2) = 1 + 3i) and (len(var3) = 1 or len(var3) = 2 + 2i)
		// note that i above is not essentially the same in each equation
		//System.out.println("lassoList = " + lassoList);
		ArrayList<BoolExpr> linearConstraints = new ArrayList<BoolExpr> ();
		// the length constraint for each var is : len(var) = k + v*i
		//ArrayList<IntExpr> vars = new ArrayList<IntExpr> ();
		for (String c: lengthVariables_.keySet()) {
			IntExpr var = lengthVariables_.get(c);
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
			IntExpr var = lengthVariables_.get(variables_.get(i));
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
		//System.out.println("solver in the testSat function: " + solver);
		Status satStatus = solver.check();
		boolean isSat = satStatus.equals(Status.SATISFIABLE);
		//System.out.println("Constraints are SAT: " + isSat);
		//final Model model = solver.getModel();
		//System.out.println(model.toString());
		//System.out.println("linearConstraints: " + linearConstraints);
		//ctx.close();
		return isSat;
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
		//System.out.println("solver in the testSat function: " + solver);
		Status satStatus = solver.check();
		boolean isSat = satStatus.equals(Status.SATISFIABLE);
		//System.out.println("Constraints are SAT: " + isSat);
		//final Model model = solver.getModel();
		//System.out.println(model.toString());
		//System.out.println("linearConstraints: " + linearConstraints);
		//ctx.close();
		return isSat;
	}

	private static void addLengthConstraintsToSolver_(List<Map<String, Integer>> lhsOfLenCons_,
			List<IntegerRelation> relLhs2RhsOfLenCons, List<Integer> rhsOfLenCons,
			Map<String, IntExpr> lengthVariables_, Context context, Solver solver) {
		// TODO Auto-generated method stub
		for (int i = 0; i < lhsOfLenCons_.size(); i++) {
			Map<String, Integer> lhsOfLenConsI_ = lhsOfLenCons_.get(i);
			IntegerRelation relLhs2RhsOfLenConsI = relLhs2RhsOfLenCons.get(i);
			int rhsOfLenConsI = rhsOfLenCons.get(i);
			IntExpr lhsI = context.mkInt(0);
			IntExpr rhsI = context.mkInt(rhsOfLenConsI);
			BoolExpr b = context.mkBool(true);
			for (String c: lhsOfLenConsI_.keySet()) {
				IntExpr x = lengthVariables_.get(c);
				IntExpr a = context.mkInt(lhsOfLenConsI_.get(c));
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
			//System.out.println(b.toString());
			solver.add(b);
		}
	}
	
	private static Map<String, IntExpr> makeLengthVariables_(Context context, ArrayList<String> variables_) {
		// TODO Auto-generated method stub
		Map<String, IntExpr> lengthVariables = new HashMap<String, IntExpr> ();
		for (String c: variables_) {
			IntExpr x = context.mkIntConst("len_" + c);
			lengthVariables.put(c, x);
		}
		return lengthVariables;
	}
	
	private static void processMembershipConstraints2_(ArrayList<String> newVariables_,
			ArrayList<ArrayList<Map<Integer, Integer>>> refinedIntegerArithDnf_,
			ArrayList<ArrayList<String>> processedLhsOfMemCons_, List<Automaton> processedRhsOfMemCons) {
		// TODO Auto-generated method stub
		Map<Integer, ArrayList<ArrayList<Automaton> > > simpleMembership = 
				getsimpleMembership_(processedLhsOfMemCons_,processedRhsOfMemCons);
		ArrayList<ArrayList<Automaton> > simpleMembershipDnf = 
				getsimpleMembershipDnf(simpleMembership);
		ArrayList<String> lhsOfMemConsCombined_ = combinelhsOfMemCons_(processedLhsOfMemCons_);
		System.out.println("processedLhsOfMemCons_: " + processedLhsOfMemCons_);
		ArrayList<ArrayList<Integer> > equalVarIds_ = getEqualVarIds_(lhsOfMemConsCombined_);
        //System.out.println(equalVarIds_);
		ArrayList<String> vars_ = getVars_(lhsOfMemConsCombined_, equalVarIds_);
		for (int i = 0; i < vars_.size(); i++) {
			newVariables_.add(i, vars_.get(i));						
		}
        //System.out.println("vars: " + vars_);
		ArrayList<ArrayList<Automaton> > simpleMembershipDnfIntersected = 
				intersectSimpleMembershipDnf(simpleMembershipDnf, equalVarIds_);
		ArrayList<ArrayList<Automaton> > oneSymbolAutomataDnf = 
				getOneSymbolAutomataDnf(simpleMembershipDnfIntersected);
		ArrayList<ArrayList<Map<Integer, Integer> > > unRefinedintegerArithDnf = 
				getIntegerArithDnf(oneSymbolAutomataDnf);
		refineIntegerArithDnf(unRefinedintegerArithDnf, refinedIntegerArithDnf_);
		
	}
	
	private static void processMembershipConstraints_(ArrayList<String> variables_,
			ArrayList<ArrayList<Map<Integer, Integer>>> refinedIntegerArithDnf_,
			ArrayList<ArrayList<String>> lhsOfMemCons_, List<Automaton> rhsOfMemCons) {
		// TODO Auto-generated method stub
		Map<Integer, ArrayList<ArrayList<Automaton> > > simpleMembership = 
				getsimpleMembership_(lhsOfMemCons_,rhsOfMemCons);
		ArrayList<ArrayList<Automaton> > simpleMembershipDnf = 
				getsimpleMembershipDnf(simpleMembership);
		ArrayList<String> lhsOfMemConsCombined_ = combinelhsOfMemCons_(lhsOfMemCons_);
		//System.out.println("lhsOfMemConsCombined_: " + lhsOfMemConsCombined_);
		ArrayList<ArrayList<Integer> > equalVarIds_ = getEqualVarIds_(lhsOfMemConsCombined_);
		//System.out.println(equalVarIds);
		ArrayList<String> vars_ = getVars_(lhsOfMemConsCombined_, equalVarIds_);
		for (int i = 0; i < vars_.size(); i++) {
			variables_.add(i, vars_.get(i));						
		}
		//System.out.println("vars: " + vars);
		ArrayList<ArrayList<Automaton> > simpleMembershipDnfIntersected = 
				intersectSimpleMembershipDnf(simpleMembershipDnf, equalVarIds_);
		ArrayList<ArrayList<Automaton> > oneSymbolAutomataDnf = 
				getOneSymbolAutomataDnf(simpleMembershipDnfIntersected);
		//System.out.println(simpleMembershipDnfIntersected.size() == oneSymbolAutomataDnf.size());
		ArrayList<ArrayList<Map<Integer, Integer> > > unRefinedintegerArithDnf = 
				getIntegerArithDnf(oneSymbolAutomataDnf);
		refineIntegerArithDnf(unRefinedintegerArithDnf, refinedIntegerArithDnf_);
		
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
	
	private static ArrayList<String> getVars_(ArrayList<String> lhsOfMemConsCombined_,
			ArrayList<ArrayList<Integer>> equalVarIds_) {
		// TODO Auto-generated method stub
		ArrayList<String> vars = new ArrayList<String> ();
		for (int i = 0; i < lhsOfMemConsCombined_.size(); i++) {
			boolean hasBeenAdded = false;
			for (int j = 0; j < equalVarIds_.size(); j++) {
				if (equalVarIds_.get(j).indexOf(i) > 0) {
					hasBeenAdded = true;
					break;
				}				
			}
			if (!hasBeenAdded) {
				vars.add(lhsOfMemConsCombined_.get(i));								
			}
		}
		return vars;
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

	private static ArrayList<ArrayList<Integer>> getEqualVarIds_(ArrayList<String> lhsOfMemConsCombined_) {
		// TODO Auto-generated method stub
		ArrayList<ArrayList<Integer>> equalVarIds = new ArrayList<ArrayList<Integer>> ();
		List<Boolean> idHasBeenAdded = new ArrayList<Boolean> ();
		for (int i = 0; i < lhsOfMemConsCombined_.size(); i++) {
			idHasBeenAdded.add(false);			
		}
		for (int i = 0; i < lhsOfMemConsCombined_.size() - 1; i++) {
			if (!idHasBeenAdded.get(i)) {
				int equalVarId = i;
				ArrayList<Integer> equalVarIdsGroup = new ArrayList<Integer> ();
				for (int j = i + 1; j < lhsOfMemConsCombined_.size(); j++) {
					if (lhsOfMemConsCombined_.get(equalVarId).equals(lhsOfMemConsCombined_.get(j))) {
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

	private static ArrayList<String> combinelhsOfMemCons_(ArrayList<ArrayList<String>> lhsOfMemCons_) {
		// TODO Auto-generated method stub
		ArrayList<String> lhsOfMemConsCombined = new ArrayList<String> ();
		for (ArrayList<String> s: lhsOfMemCons_) {
			lhsOfMemConsCombined.addAll(s);			
		}
		return lhsOfMemConsCombined;
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
	
	private static Map<Integer, ArrayList<ArrayList<Automaton>>> getsimpleMembership_(
			ArrayList<ArrayList<String>> lhsOfMemCons_, List<Automaton> rhsOfMemCons) {
		// TODO Auto-generated method stub
		HashMap<Integer, ArrayList<ArrayList<Automaton> > > simpleMembership = 
				new HashMap<Integer, ArrayList<ArrayList<Automaton> > >();
		for (int i = 0; i < lhsOfMemCons_.size(); i++) {
			int noOfVars = lhsOfMemCons_.get(i).size();
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
	
	public static ArrayList<ArrayList<Integer> > getPermutations2(int numOfStates, int size) {
		ArrayList<ArrayList<Integer> > permutations = new ArrayList<ArrayList<Integer> >();
		ArrayList<Integer> permutation = new ArrayList<Integer>();
		for (int i = 0; i < size; i++) {
			permutation.add(0);
		}
		int j = size - 1;
		while(true) {
			for(int i = 0; i <= numOfStates; i++) {
				permutation.set(j, i);
				//System.out.println(permutation.toString());
				ArrayList<Integer> permutationCopy = new ArrayList<>(permutation);
				permutations.add(permutationCopy);
				//System.out.println(result.toString());
			}
			int k = j - 1;
			while(k >= 0 && permutation.get(k) == numOfStates) {
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
		//System.out.println("similarIdMapValues : " + similarIdMapValues.toString());
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
