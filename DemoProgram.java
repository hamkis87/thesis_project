import java.util.*;

import dk.brics.automaton.*;

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
			System.out.println("stateList[" + stateId + "] : " + stateList.get(stateId));
			stateId++;
		}
		int initialStateId = stateList.indexOf(a.getInitialState());
		Automaton newAutomaton = getAutomatonFromStates(initialStateId, stateList);
		System.out.println("New Automaton = " + newAutomaton.getStates());
		System.out.println("Equal Automata : " + newAutomaton.equals(c));


		List<Character> states = Arrays.asList('a', 'b', 'c', 'd');
		int permutationSize = 3;
		ArrayList<ArrayList<Integer> > permutations = getPermutations(states.size(), permutationSize);
		//System.out.println("Permutation: " + permutations.toString());
		ArrayList<ArrayList<Automaton> > allAutomata = getAllAutomata(initialStateId, stateList, permutations, permutationSize);
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
	
	/*
	 * public static ArrayList<ArrayList<Character> >
	 * getAutomataPermutations(ArrayList<ArrayList<Integer> > permutations, int
	 * permutationSize, List<Character> states) { ArrayList<ArrayList<Character> >
	 * automataPermutations = new ArrayList<ArrayList<Character> >(); for (int
	 * automataPermutationId = 0; automataPermutationId < permutations.size();
	 * automataPermutationId++) { ArrayList<Character> automataPermutation = new
	 * ArrayList<Character>(); ArrayList<Integer> permutation =
	 * permutations.get(automataPermutationId); for (int variableId = 0; variableId
	 * < permutationSize; variableId++) {
	 * automataPermutation.add(states.get(permutation.get(variableId))); }
	 * System.out.println(automataPermutation.toString());
	 * automataPermutations.add(automataPermutation); } return automataPermutations;
	 * }
	 */
	
	public static Automaton getAutomatonFromStates(int initialStateId, List<State> stateList) {
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
