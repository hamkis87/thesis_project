import java.util.*;

import dk.brics.automaton.*;

/**
 * @author hamid
 *
 */
public class DemoProgram {

	public static void main(String[] args) {		
		RegExp r1 = new RegExp("ab(c|d)*");
		RegExp r2 = new RegExp("ab(c)*");
		Automaton a = r1.toAutomaton();
		Automaton c = r2.toAutomaton();
		Automaton b = a.clone();
		b.restoreInvariant();
		b.setDeterministic(true);
		int numOfStates = a.getNumberOfStates();
		System.out.println("Start State : " + a.getInitialState());
		List<State> stateList = new ArrayList<State>(numOfStates);
		int stateId = 0;
		for (State s :  a.getStates()) {
			stateList.add(stateId, s);
			//System.out.println("State = " + s.toString());
			//this printout is to check each state i is of order i in the set 
			System.out.println("stateList[" + stateId + "] : " + stateList.get(stateId));
			stateId++;
		}
		int initialStateId = stateList.indexOf(a.getInitialState());
		int permutationSize = 3;
		ArrayList<ArrayList<Integer> > permutations = getPermutations(stateList.size(), permutationSize);
		//System.out.println("Permutation: " + permutations.toString());
		ArrayList<ArrayList<Automaton> > allAutomata = getAllAutomata(initialStateId, stateList, 
				                                                      permutations, permutationSize);
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
				Automaton automaton = getAutomatonFromStates(automatonInitialStateId, automatonAcceptStateId, stateList);
				conjunctionOfAutomata.add(variableId, automaton);
				// the automaton of the next variable starts at the accept state of the previous
				// variable's automaton
				automatonInitialStateId = automatonAcceptStateId;
				//System.out.println("Variable no: " + variableId + " has automaton: " + automaton.toString());
				variableId++;				
			}
			// the automaton of the last variable has the accept state(s) of the original automaton 
			Automaton automaton = getAutomatonFromStates(automatonInitialStateId, -1, stateList);
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
	public static Automaton getAutomatonFromStates(int initialStateId, int acceptStateId,  List<State> stateList) {
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
			for (Transition oldTransition :  oldStateTransitions) {
				State oldStateNext = oldTransition.getDest();
				char t_min = oldTransition.getMin();
				char t_max = oldTransition.getMax();
				//System.out.println(oldStateNext);
				int oldStateNextId = stateList.indexOf(oldStateNext);
				int newStateNextId = oldStateNextId;
				State newStateNext = stateList2.get(newStateNextId);
				Transition newTransition = new Transition(t_min, t_max, newStateNext);
				newState.addTransition(newTransition);								
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
		return newAutomaton;
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
}
