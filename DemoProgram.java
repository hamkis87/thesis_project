import java.util.*;

import dk.brics.automaton.*;

/**
 * @author hamid
 *
 */
public class DemoProgram {

	public static void main(String[] args) {
		//readUserInput();
		//testLassoAsLinearConstraint();
		readUserInput();
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
		String lhsOfStrCons1 = "ac";
		String lhsOfStrCons2 = "fa";
		String lhsOfStrCons3 = "gbe";
		String lhsOfStrCons4 = "c";
		String lhsOfStrCons5 = "bd";
		RegExp r1 = new RegExp("xy(w|z)*");
		RegExp r2 = new RegExp("(xy)*");
		RegExp r3 = new RegExp("(w|z)*");
		RegExp r4 = new RegExp("(wz)*");
		RegExp r5 = new RegExp("(xyz)*");
		Automaton rhsOfStrCons1 = r1.toAutomaton();
		Automaton rhsOfStrCons2 = r2.toAutomaton();
		Automaton rhsOfStrCons3 = r3.toAutomaton();
		Automaton rhsOfStrCons4 = r4.toAutomaton();
		Automaton rhsOfStrCons5 = r5.toAutomaton();
		List<String> lhsOfStrCons = new ArrayList<String> ();
		List<Automaton> rhsOfStrCons = new ArrayList<Automaton> ();
		lhsOfStrCons.add(0, lhsOfStrCons1);
		lhsOfStrCons.add(1, lhsOfStrCons2);
		lhsOfStrCons.add(2, lhsOfStrCons3);
		lhsOfStrCons.add(3, lhsOfStrCons4);
		lhsOfStrCons.add(4, lhsOfStrCons5);
		//System.out.println("lhsOfMembershipCons: " + lhsOfMembershipCons);
		rhsOfStrCons.add(0, rhsOfStrCons1);
		rhsOfStrCons.add(1, rhsOfStrCons2);
		rhsOfStrCons.add(2, rhsOfStrCons3);
		rhsOfStrCons.add(3, rhsOfStrCons4);
		rhsOfStrCons.add(4, rhsOfStrCons5);	
		//System.out.println("rhsOfMembershipCons: " + rhsOfMembershipCons);
		Map<Integer, ArrayList<ArrayList<Automaton> > > simpleMembership = 
				getsimpleMembership(lhsOfStrCons,rhsOfStrCons);
		ArrayList<ArrayList<Automaton> > simpleMembershipDnf = 
				getsimpleMembershipDnf(simpleMembership);
		String lhsOfStrConsCombined = combineLhsOfStrCons(lhsOfStrCons);
		System.out.println(lhsOfStrConsCombined);
		ArrayList<ArrayList<Integer> > equalVarIds = getEqualVarIds(lhsOfStrConsCombined);
		System.out.println(equalVarIds);
		String vars = getVars(lhsOfStrConsCombined, equalVarIds); 
		System.out.println(vars);
		ArrayList<ArrayList<Automaton> > simpleMembershipDnfIntersected = 
				intersectSimpleMembershipDnf(simpleMembershipDnf, equalVarIds);
		ArrayList<ArrayList<Automaton> > oneSymbolAutomataDnf = 
				getOneSymbolAutomataDnf(simpleMembershipDnfIntersected);
		System.out.println(simpleMembershipDnfIntersected.size() == oneSymbolAutomataDnf.size());
				
				
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
	
	public static String getVars(String lhsOfStrConsCombined, ArrayList<ArrayList<Integer> > equalVarIds) {
		String vars = "";
		for (int i = 0; i < lhsOfStrConsCombined.length(); i++) {
			boolean hasBeenAdded = false;
			for (int j = 0; j < equalVarIds.size(); j++) {
				if (equalVarIds.get(j).indexOf(i) > 0) {
					hasBeenAdded = true;
					break;
				}				
			}
			if (!hasBeenAdded) {
				vars = vars + lhsOfStrConsCombined.charAt(i);								
			}
		}
		return vars;
	}
	
	public static ArrayList<ArrayList<Integer> > getEqualVarIds(String lhsOfStrConsCombined) {
		ArrayList<ArrayList<Integer> > equalVarIds = new ArrayList<ArrayList<Integer> > ();
		List<Boolean> idHasBeenAdded = new ArrayList<Boolean> ();
		for (int i = 0; i < lhsOfStrConsCombined.length(); i++) {
			idHasBeenAdded.add(false);			
		}
		for (int i = 0; i < lhsOfStrConsCombined.length() - 1; i++) {
			if (!idHasBeenAdded.get(i)) {
				int equalVarId = i;
				ArrayList<Integer> equalVarIdsGroup = new ArrayList<Integer> ();
				for (int j = i + 1; j < lhsOfStrConsCombined.length(); j++) {
					if (lhsOfStrConsCombined.charAt(equalVarId) == lhsOfStrConsCombined.charAt(j)) {
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
	
	public static String combineLhsOfStrCons(List<String> lhsOfStrCons) {
		String lhsOfStrConsCombined = "";
		for (String s: lhsOfStrCons) {
			lhsOfStrConsCombined = lhsOfStrConsCombined.concat(s);			
		}
		return lhsOfStrConsCombined;
	}
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
	              getsimpleMembership(List<String> lhsOfStrCons, List<Automaton> rhsOfStrCons) {
		HashMap<Integer, ArrayList<ArrayList<Automaton> > > simpleMembership = 
				new HashMap<Integer, ArrayList<ArrayList<Automaton> > >();
		for (int i = 0; i < lhsOfStrCons.size(); i++) {
			int noOfVars = lhsOfStrCons.get(i).length();
			Automaton automaton = rhsOfStrCons.get(i);
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
		return result;
	}

	public static void testLassoAsLinearConstraint() {
		RegExp r = new RegExp("(aaaa|bss)*");
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