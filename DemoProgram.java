import java.util.*;
import java.util.logging.Logger;
import java.util.stream.Collectors;

import dk.brics.automaton.*;
import com.microsoft.z3.*;
import java.io.*;
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
		ArrayList<ArrayList<String>> lhsOfMemCons = new ArrayList<ArrayList<String>> () ;
		List<Automaton> rhsOfMemCons = new ArrayList<Automaton> ();
		List<Map<String, Integer>> lhsOfLenCons_ = new ArrayList<Map<String, Integer>> ();
		List<Integer> rhsOfLenCons = new ArrayList<Integer> ();
		List<IntegerRelation> relLhs2RhsOfLenCons = new ArrayList<IntegerRelation> ();
		try {
            //opening file for reading in Java
            String file = "/home/hamid/eclipse-workspace/DemoProject/src/test.txt";
            BufferedReader reader = new BufferedReader(new FileReader(file));
            getMemConstraints(reader, lhsOfMemCons, rhsOfMemCons);
            getLengthConstraints_(reader, lhsOfLenCons_, relLhs2RhsOfLenCons, rhsOfLenCons);
            //System.out.println("lhsOfMemCons " + lhsOfMemCons);
	        //System.out.println("rhsOfMemCons " + rhsOfMemCons);
            //reading file content line by line
//            String line = reader.readLine();
//            String[] lineArray = line.split(":");
//            System.out.println(Arrays.toString(lineArray));
//            System.out.println("lineArray[0] " + lineArray[0]);
//            String lenConsName = "#length_constraints";
//            int noOfLenCons = Integer.parseInt(lineArray[1]);
//            System.out.println(noOfLenCons);
//            int noOfConsRead = 0;
//            while(noOfConsRead < noOfLenCons){
//            	line = reader.readLine();
//            	System.out.println(line);
//  	            String[] data = line.split("\t");
//  	            System.out.println(Arrays.toString(data));
//  	          noOfConsRead++;
//  	        }
//            while((line = reader.readLine()) != null){
//                System.out.println(line);
//        	    String[] data = line.split("\t");
//        	    System.out.println(Arrays.toString(data));
//            }
            reader.close();
                 
        } catch (FileNotFoundException ex) {
            System.out.println("File not found");
        } catch (IOException ex) {
        	System.out.println("IO exception");
        }	
		//testNoDelimiters();
		//splitExample();
	}
	
	private static void getLengthConstraints_(BufferedReader reader, List<Map<String, Integer>> lhsOfLenCons_,
			List<IntegerRelation> relLhs2RhsOfLenCons, List<Integer> rhsOfLenCons) {
		// TODO Auto-generated method stub
		try {
			String line;
			line = reader.readLine();
	        String[] lineArray = line.split(":");
	        System.out.println(Arrays.toString(lineArray));
	        String lenConsName = "#length_constraints";
            int noOfLenCons = Integer.parseInt(lineArray[1]);
            System.out.println(noOfLenCons);
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
		        	System.out.println(leftTerm);
		        	String[] termContents = leftTerm.split(" ");
		            System.out.println(Arrays.toString(termContents));
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
		        
		        System.out.println(Arrays.toString(data));
		        noOfConsRead++;
	        }
            System.out.println(relLhs2RhsOfLenCons);
            System.out.println(lhsOfLenCons_);
            System.out.println(rhsOfLenCons);
        }
		catch (FileNotFoundException ex) {
			System.out.println("File not found");
        } 
		catch (IOException ex) {
			System.out.println("IO exception");
    	}
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
		        RegExp rhsOfMemConsRegexI = new RegExp(data[1]);
		        //System.out.println("rhsOfMemConsRegexIStr " + data[1]);
		        //System.out.println("rhsOfMemConsRegexI " + rhsOfMemConsRegexI);
		        Automaton rhsOfMemConsI = rhsOfMemConsRegexI.toAutomaton();
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
	
	public static void testNoDelimiters() {
	    String sourceString = "This is a\nsample of\nnew big line-with\ttabs and\rcarriage-returns";
	    System.out.println("Source String is ");
	    System.out.println(sourceString);
	    // uses default set of characters as delimiters
	    StringTokenizer st = new StringTokenizer(sourceString);
	    while (st.hasMoreTokens()) {
	        System.out.println("testNoDelimiters : Next-Token = " + st.nextToken());
	    }
	    System.out.println(" ------------------------------------------------------------------------------ ");
	    // uses space character as a delimiter; this
	    // will disregard the default delimiter character set
	    st = new StringTokenizer(sourceString, " ");
	    while (st.hasMoreTokens()) {
	        System.out.println("testSpaceDelimiter : Next-Token = " + st.nextToken());
	        }
	    }
	
	public static void splitExample() {
		String memcons = "xym\t(a|b|c)*";  
	    String player = "1||1||Abdul-Jabbar||Karim||1996||1974";
	    String[] data = memcons.split("\t");
	    System.out.println(Arrays.toString(data));
	}
}