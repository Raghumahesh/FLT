import java.io.*;
import java.util.*;

public class Prog2 {
    public static void main(String[] args) {
        if (args.length != 1) {
            System.out.println("One file argument is needed");
            return;
        }

        // Reading the dfsm file from the command line arguments 
        String dfsfile = args[0];

        try {

            // Taking Required datastructures that are needed to store the dfsm file specification like
            // hashmap<integer, hashmap<>> for table and hashset for final states and arraylist for alphabets.
            HashMap<Integer, HashMap<String, Integer>> transistionTable = new HashMap<>();
            HashSet<Integer> finalStates = new HashSet<>();
            ArrayList<String> alphabets = new ArrayList<>();

            BufferedReader bufferedReader = new BufferedReader(new FileReader(dfsfile));
            String line;
            boolean fileRead = true;

            while ((line = bufferedReader.readLine()) != null) {
                if (!line.equals("")) {
                    fileRead = false;
                    break;
                }
            }

            if (fileRead) {
                System.out.println("The DFSM file is empty.");
                return;
            }

           // alphabets are stored in the arrayList.
           while(!line.equals("")){
            List<String> tempstr = splitLine(line, ' ');
            for(String t: tempstr){
                alphabets.add(t);
            }
            line = bufferedReader.readLine();
           }

            int stateNumber = 1;
            int lineCount = 1;
            Boolean check = false;
            // This highest value is used for checking the if any invalid transistion table values are given.
            int highestval =0;
            int rowcount =0;
            // Second segment is for reading the transition table.
            while ((line = bufferedReader.readLine()) != null) {
                if (line.equals("")) {
                    lineCount++;
                    if (lineCount > 1 && check) break;
                    if(lineCount > 1 && !check){
                        System.out.println("There are more than one empty line between first and second segments"); 
                        return;
                    } // More than one empty line means we're done
                    continue;
                }
                check = true;
                HashMap<String, Integer> stateTransition = new HashMap<>();
                ArrayList<String> states = splitLine(line, ' ');
                
                if (alphabets.size() != states.size()) {
                    System.out.println("REJECT");
                    return;
                }
                
                for (int i = 0; i < alphabets.size(); i++) {
                    stateTransition.put(alphabets.get(i), Integer.parseInt(states.get(i)));
                } 
                transistionTable.put(stateNumber, stateTransition);
                stateNumber++;
                // Here I am checking the if the valid transition table is there or not according to row numbers. 
                for (int i = 0; i < alphabets.size(); i++) {
                    int nextState = Integer.parseInt(states.get(i));
                    if (nextState > highestval) {
                        highestval = nextState;
                    }
                }
                rowcount++;
            }

            if (highestval > rowcount) {
                System.out.println("In valid data in Transistion Table");
                return;
            }
            
            // This part is for the third segment to store the final states that is present in the last non-empty
            // line of the dfsm file.
            while ((line = bufferedReader.readLine()) != null) {
                ArrayList<String> finalStr = splitLine(line, ' ');
                for (String state : finalStr) {
                    int finalState = Integer.parseInt(state);
                    if (!transistionTable.containsKey(finalState)) {
                        System.out.println("Invalid final state");
                        return;
                    }
                    finalStates.add(Integer.parseInt(state));
                }
            }
            // Here I am checking if there are no final states then, the program should give the output regression as phi
            if (finalStates.size() == 0) {
                System.out.println("phi");
                return;
            }
            Set<Integer> visitedStates = new HashSet<>();
            // According to the Algorithm given in the textbook, first I used the dfs algorithm to find the
            // unreachable states in the dfsm that is formed.
            dfs(1, transistionTable, visitedStates); 

            // when the function work is done, it gets the all reachable states from 1 in the set. here in the below step
            // I am getting the unreachable states.
            List<Integer> removingunreachable = new ArrayList<>();
            for (Integer state : transistionTable.keySet()) {
                if (!visitedStates.contains(state)) {
                    removingunreachable.add(state);
                }
            }
            
            for (Integer state : removingunreachable) {
                transistionTable.remove(state);
            }
            
       

            // The second step is to create a new start state and new final state and map them to eps-transitions from those states
            // to the old start state and old final states.
            int newStartState = 0;
            int newFinalState = stateNumber;

            transistionTable.put(newStartState, new HashMap<>());
            transistionTable.get(newStartState).put("eps", 1);

            transistionTable.put(newFinalState, new HashMap<>());

            for (int fin : finalStates) {
                if (transistionTable.get(fin) == null) {
                    transistionTable.put(fin, new HashMap<>());
                }
                transistionTable.get(fin).put("eps", newFinalState);
            }
            finalStates.clear();

            // updating the final states.
            finalStates.add(newFinalState);

            System.out.println(transistionTable);

            // Now, After I update the transition table, I get the incoming and outgoing states for every state in the finite state machine

            HashMap<Integer, HashMap<Integer, String>> incoming = getIncoming(transistionTable, alphabets);
            HashMap<Integer, HashMap<Integer, String>> outgoing = getOutgoing(transistionTable, alphabets);
        
            //System.out.println("Incoming Map: " + incoming);
            //System.out.println("Outgoing Map: " + outgoing);
            // System.out.println(finalStates);

            // After I get the incoming and outgoing states, I pass through this function which eliminates each state one by one.
            for (int i =newFinalState-1 ; i >=1; i--) {
                eliminateState(i, incoming, outgoing);
            }

            // I am getting the final Regular Expression between the start state and final state.
            String finalRegex = incoming.get(newFinalState).get(newStartState);
            if (finalRegex == null) {
                System.out.println("phi"); 
            } else {
                System.out.println("The Regular expression is: " + finalRegex);
            }
            //System.out.println(incoming);
            //System.out.println(outgoing);
        } 
        catch (IOException e) {
            e.printStackTrace();
        }
    }

    // The function DFS to find the unreachable states through 1 are found here.
    public static void dfs(Integer startState, HashMap<Integer, HashMap<String, Integer>> transitionTable, Set<Integer> visitedStates) {
        // Here I am using the transition table and visited state integer hashset that stores the visited statenumber from start state.
        visitedStates.add(startState);
        
        HashMap<String, Integer> transitions = transitionTable.get(startState);
        if (transitions == null) return;
    // I am checking all the reachable states from 1 and storing them into the visited set.
        for (Integer nextState : transitions.values()) {
            if (!visitedStates.contains(nextState)) {
                dfs(nextState, transitionTable, visitedStates);
            }
        }
    }

    //This is function where each state is removed and their corresponded updated values of transitions are stored.
    private static void eliminateState(int state, HashMap<Integer, HashMap<Integer, String>> incoming,HashMap<Integer, HashMap<Integer, String>> outgoing) 
    {
        if (!incoming.containsKey(state) || !outgoing.containsKey(state)) {
            return;
        }
        //Getting the incomings and outgoings of each state that is going to be eliminated.
        HashMap<Integer, String> incomingTransitions = incoming.get(state);
        HashMap<Integer, String> outgoingTransitions = outgoing.get(state);
        
        //Checking for self transition with in the incoming states.
        String selfstring = incomingTransitions.getOrDefault(state, "");
        if (!selfstring.isEmpty()) {
            selfstring = "(" + selfstring + ")*";
        }

        // Loop through each pair of incoming and outgoing states for the eliminated state.
        for (Integer income : incomingTransitions.keySet()) {
            if(state == income){
                continue;
            }
            for (Integer outcome : outgoingTransitions.keySet()) {

                if(state == outcome){
                    continue;
                }
                //Getting the incoming alphabet and outgoing alphabet
                String incomingstring = incomingTransitions.get(income);
                String outgoingstring = outgoingTransitions.get(outcome);
                
                // Combining the incoming, self-loop, and outgoing regexes
                String newRegex;
                if (selfstring.isEmpty()) {
                    newRegex = incomingstring + "." + outgoingstring;
                } else {
                    newRegex = incomingstring + "." + selfstring + "." + outgoingstring;
                }
                                
                // Here checking if already there is a exisiting transition from the state and doing union.
                if (incoming.containsKey(outcome) && incoming.get(outcome).containsKey(income)) {
                    HashMap<Integer,String> tx = incoming.get(outcome);
                    String existingRegex = tx.get(income);
                    newRegex = existingRegex + "+" + newRegex;
                    tx.put(income, newRegex);
                    incoming.put(outcome, tx);
                }
                // If there is no such thing there, directly put out to incoming map
                else if(incoming.containsKey(outcome)){
                    HashMap<Integer,String> tx = incoming.get(outcome);
                    tx.put(income, newRegex);
                    incoming.put(outcome, tx);
                }
                else{
                    HashMap<Integer, String> tx = new HashMap<Integer, String>();
                    tx.put(income, newRegex);
                    incoming.put(outcome, tx);
                }

                // Following the same for the outgoing map also, where I am checking if any existing transitions are there, then I am doing union.
                if (outgoing.containsKey(income) && outgoing.get(income).containsKey(outcome)) {
                    HashMap<Integer,String> tx = outgoing.get(income);
                    String existingRegex = tx.get(outcome);
                    newRegex = existingRegex  + "+" + newRegex;
                    tx.put(outcome, newRegex);
                    outgoing.put(income, tx);
                }
                else if(outgoing.containsKey(income)){
                    HashMap<Integer,String> tx = outgoing.get(income);
                    tx.put(outcome, newRegex);
                    outgoing.put(income, tx);
                }
                else{
                    HashMap<Integer, String> tx = new HashMap<Integer, String>();
                    tx.put(outcome, newRegex);
                    outgoing.put(income, tx);
                }

            }
        }
        // After updating where thing incoming and outgoing map, I am removing them, so to avoid confusion the transitions of the state to be eliminated.
        incoming.remove(state);

        for (HashMap<Integer, String> map : incoming.values()) {
            map.remove(state);
        }
        outgoing.remove(state);
        for (HashMap<Integer, String> map : outgoing.values()) {
            map.remove(state);
        }


    }

    // Here I am using this function to get the incoming transitions for all the states that are present in the fsm.
    public static HashMap<Integer, HashMap<Integer, String>> getIncoming(HashMap<Integer, HashMap<String, Integer>> transitionTable, ArrayList<String> alphabets) {
        HashMap<Integer, HashMap<Integer, String>> incoming = new HashMap<>();
    
        for (Integer source : transitionTable.keySet()) {
            for (String str : transitionTable.get(source).keySet()) {
                Integer dest = transitionTable.get(source).get(str);
    
                if (!incoming.containsKey(dest)) {
                    incoming.put(dest, new HashMap<>());
                }
    
                String exittransition = incoming.get(dest).getOrDefault(source, "");
    
                if (exittransition.isEmpty()) {
                    incoming.get(dest).put(source, str);
                } else {
                    String newTransition = "(" + exittransition + ")" + "+" + "(" + str + ")";
                    incoming.get(dest).put(source, newTransition);
                }
            }
        }
    
        return incoming;
    }
    
    // Function to generate the outgoing transitions for all the states in the fsm.
    public static HashMap<Integer, HashMap<Integer, String>> getOutgoing(HashMap<Integer, HashMap<String, Integer>> transitionTable, ArrayList<String> alphabets) {
        HashMap<Integer, HashMap<Integer, String>> outgoing = new HashMap<>();
    
        for (Integer source : transitionTable.keySet()) {

            if (!outgoing.containsKey(source)) {
                outgoing.put(source, new HashMap<>());
            }
    
            for (String str : transitionTable.get(source).keySet()) {
                Integer dest = transitionTable.get(source).get(str);
    
                // Skipping the outgoing transitions that is going to same state.
                if (source.equals(dest)) {
                    continue;
                }
    
                String exittransition = outgoing.get(source).getOrDefault(dest, "");
    
                if (exittransition.isEmpty()) {
                    outgoing.get(source).put(dest, str);
                } else {
                    String newTransition = "(" + exittransition + ")" + "+" + "(" + str + ")";
                    outgoing.get(source).put(dest, newTransition);
                }
            }
        }
    
        return outgoing;
    }
    
    
    

    public static ArrayList<String> splitLine(String str, char ch) {
        ArrayList<String> result = new ArrayList<>();
        int start = 0;

        for (int j = 0; j < str.length(); j++) {
            if (str.charAt(j) == ch) {
                if (start != j) {
                    result.add(str.substring(start, j));
                }
                start = j + 1;
            }
        }

        if (start != str.length()) {
            result.add(str.substring(start));
        }

        return result;
    }
        
}
