// Name: Raghu Medarametla
// CWID: A20386265
// Course: Formal Language Theory
// Due Date: 10/26/2023
// Date of Submission: 10/26/2023
// Assignment Number: 4

import java.io.*;
import java.util.*;

//Program Class
public class p4 {
    public static void main(String[] args) {
        if (args.length != 2) {
            System.out.println("Give input file name and output file name");
            return;
        }
        //Get the input file name from the argument.
        String filename = args[0];
        //Taking this HashMap to store the context free grammar given in the input file.
        Map<String, List<String>> cfgMap = new HashMap<>();

        // I am using below buffered reader to read line by line.
        try (BufferedReader reader = new BufferedReader(new FileReader(filename))) {
            String line;
            String nonterminal = null;
            String startSymbol=null;

            while ((line = reader.readLine()) != null) {
                line = line.trim();

                if (line.isEmpty()) {
                    continue;
                }

                // I am seperating the left side and right side production by "::="
                String[] parts = line.split("::=");

                String leftSide = parts[0].trim();
                String rightSide;
                
                //If right is empty then I am making it is as eps.
                if (parts.length > 1) {
                    rightSide = parts[1].trim();
                } else {
                    rightSide = "eps";
                }
                //Storing the left side values
                if (!cfgMap.containsKey(leftSide)) {
                    cfgMap.put(leftSide, new ArrayList<>());
                    nonterminal = leftSide;
                }
                //Storing the right side values.
                if (nonterminal != null && nonterminal.equals(leftSide)) {
                    cfgMap.get(leftSide).add(rightSide);
                }
                //Storing the Start symbol.
                if (startSymbol == null) {
                    startSymbol = leftSide;
                }
            }
            //Now I am calling the three functions one by one to make a change to the given input file.
            removeUnreachable(cfgMap,startSymbol);
            removeUnproductive(cfgMap);
            removeEps(cfgMap,startSymbol);

            //System.out.println(cfgMap);
            List<String> nonterminalsToRemove = new ArrayList<>();
            for (String nonter : cfgMap.keySet()) {
                if (cfgMap.get(nonter).isEmpty()) {
                    nonterminalsToRemove.add(nonter);
                }
            }
            
            for (String nonter : nonterminalsToRemove) {
                cfgMap.remove(nonter);
            }
            // Remove non-terminals from other productions
            for (String non_terminal : nonterminalsToRemove) {
                for (String otherNonterminal : cfgMap.keySet()) {
                    List<String> productions = cfgMap.get(otherNonterminal);
                    List<String> updatedProductions = new ArrayList<>();
                    for (String production : productions) {
                        if (!production.contains(non_terminal)) {
                            updatedProductions.add(production);
                        }
                    }
                    cfgMap.put(otherNonterminal, updatedProductions);
                }
            }
            
            //System.out.println(cfgMap);
            String outputFileName = args[1];

            try (PrintWriter writer = new PrintWriter(outputFileName)) {
                // Write the start symbol components if they exist
                if (cfgMap.containsKey("S*")) {
                    List<String> startSymbolProductions = cfgMap.get("S*");
                    for (String production : startSymbolProductions) {
                        if (production.equals("eps")) {
                            writer.println("<" + "S*" + "> ::=");
                        } else {
                            writer.println("<" + "S*" + "> ::= " + production);
                        }
                    }
                }
        
        
                // Write the rest of the CFG
                for (String nonterm : cfgMap.keySet()) {
                    if (!nonterm.equals("S*")) {
                        List<String> productions = cfgMap.get(nonterm);
                        for (String production : productions) {
                            if (production.equals("eps")) {
                                writer.println(nonterm + " ::=");
                            } else {
                                writer.println(nonterm + " ::= " + production);
                            }
                        }
                    }
                }
            } catch (IOException e) {
                System.out.println("Error writing to the output file.");
            }

        } catch (IOException e) {
            System.out.println("Error");
        }
    }


    // This function is to remove epsilons from the context free grammaer
    private static void removeEps(Map<String, List<String>> cfgMap, String startSymbol) {

        // First I want to find the nullable variables in the context free grammar.
        Set<String> nullableSet = new HashSet<>();

        // Whenever I came across a X-> eps then I am adding that X non-terminal to the nullable set.
        for (String nonterminal : cfgMap.keySet()) {
            for (String production : cfgMap.get(nonterminal)) {
                if (production.equals("eps")) {
                    nullableSet.add(nonterminal);
                }
            }
        }
        // Next this while loop is carried out until we don't add any nullable variables.
        // we are checking if the nonterminals which are nullable are being in Right hand side is being generated from a non terminal then the corresponding non-terminal should be also added to nullable sets.
        boolean changed;

        do {
            changed = false;
    
            for (String nonterminal : cfgMap.keySet()) {
                for (String production : cfgMap.get(nonterminal)) {
                    List<String> segments = splitProduction(production);
                    boolean isProductionNullable = true;
    
                    for (String segment : segments) {
                        if (!nullableSet.contains(segment)) {
                            isProductionNullable = false;
                            break;
                        }
                    }
    
                    if (isProductionNullable && !nullableSet.contains(nonterminal)) {
                        nullableSet.add(nonterminal);
                        changed = true;
                    }
                }
            }
    
        } while (changed);
    
        //System.out.println(nullableSet);

        // Here I am checking the each productions right hand side, if a particular non terminal is nullable then we need to remove 
        // that non terminal form a string and add it to the newadditonal production set.
        boolean change;
        do{
            change =false;

            for(String nonterminal : cfgMap.keySet()){
                HashSet<String> newadditionProd = new HashSet<String>();
                List<String> listOfProductions = cfgMap.get(nonterminal); 
                for(String production: listOfProductions){
                    List<String> segments = splitProduction(production);
                    //System.out.println(segments);
                    for(int i=0;i<segments.size();i++){
                        if(nullableSet.contains(segments.get(i))){
                            String  strtempNew = "";

                            for(int j=0;j< segments.size();j++){
                                if(j!= i){
                                    strtempNew += segments.get(j);
                                }
                            }
                            // I am adding into newproductions set checking the cases:
                            // 1. if the newstring is not equal to ""
                            // 2. if the newstring is not equal to eps
                            // 3. if new string is not present already present productions
                            // 4. if newstring isequal to it own self.
                            if(!strtempNew.equalsIgnoreCase("") && !strtempNew.equalsIgnoreCase("eps") 
                                    && !listOfProductions.contains(strtempNew) && !newadditionProd.contains(strtempNew) && !strtempNew.equalsIgnoreCase(nonterminal)){
                                        newadditionProd.add(strtempNew);
                                        change = true;
                                    }

                        }
                    }
                }

                for(String st: newadditionProd){
                    listOfProductions.add(st);
                }
                cfgMap.put(nonterminal, listOfProductions);
            }


        }while(change);

        for(String nonterminal : cfgMap.keySet()){
                List<String> listOfProductions = cfgMap.get(nonterminal);
                if(listOfProductions.contains("eps")){
                    listOfProductions.remove("eps");
                    cfgMap.put(nonterminal, listOfProductions);
                }
        }


        if(nullableSet.contains(startSymbol)){
            List<String> newprod = new ArrayList<String>();
            newprod.add("eps");
            newprod.add(startSymbol);
            cfgMap.put("S*", newprod);
        }

    }
    

    // The fucntion is used to remove unproductive values i.e. the left side production that does not produce a termianl string.
    private static void removeUnproductive(Map<String, List<String>> cfgMap) {

        // Here I am keeping a Hash set to keep productive nonterminals
        Set<String> productiveNonterminals = new HashSet<>();
        Set<String> allNonterminals = cfgMap.keySet();

        // In this while loop I will constantly check if the each non-terminal produces a terminal string. If the mom terminal that is on the right side production
        // of the context free grammar, then I am making the left side non-terminal also as the productive non-terminal
        boolean changed;
        do {
            changed = false;
            for (String nonterminal : allNonterminals) {
                if (!productiveNonterminals.contains(nonterminal)) {
                    for (String production : cfgMap.get(nonterminal)) {
                        List<String> segments = splitnonTerminal(production);
                        boolean isProductionProductive = true;
                        for (String segment : segments) {
                            if (!productiveNonterminals.contains(segment)) {
                                isProductionProductive = false;
                                break;
                            }
                        }

                        if (isProductionProductive) {
                            // Here I am doing that logic where the right side non terminal is productive, so this carries out until
                            // any new symbol is added to productive nonterminal set.
                            productiveNonterminals.add(nonterminal);
                            changed = true;
                            break;
                        }
                    }
                }
            }
        } while (changed);

        //System.out.println(productiveNonterminals);
        // Remove unproductive symbols from the CFG
        for (String nonterminal : new HashSet<>(cfgMap.keySet())) {
            if (!productiveNonterminals.contains(nonterminal)) {
                cfgMap.remove(nonterminal);
            } else {
                List<String> productions = cfgMap.get(nonterminal);
                List<String> newProductions = new ArrayList<>();
                for (String production : productions) {
                    List<String> segments = splitnonTerminal(production);
                    //System.out.println(segments);
                    boolean isProductionProductive = true;
                    for (String segment : segments) {
                        if (!productiveNonterminals.contains(segment)) {
                            isProductionProductive = false;
                            break;
                        }
                    }
                    if (isProductionProductive) {
                        newProductions.add(production);
                    }
                }
                cfgMap.put(nonterminal, newProductions);
            }
        }
    }


    //Here I implemented the function to remove unreachable states.
    private static void removeUnreachable(Map<String, List<String>> cfgMap, String startSymbol) {

        // I am keeping a map of the reachable non terminals in a set.
        Set<String> reachableNonterminals = new HashSet<>();
        Set<String> allNonterminals = cfgMap.keySet();
    
        // Mark the start symbol as reachable
        reachableNonterminals.add(startSymbol);
    
        // I am checking through each nonterminal that can be reached from the start state.
        boolean changed;
        do {
            changed = false;
            for (String nonterminal : allNonterminals) {
                if (reachableNonterminals.contains(nonterminal)) {
                    for (String production : cfgMap.get(nonterminal)) {
                        // Split the production into segments enclosed within <>
                        // This splits the right side production values that contains non terminals.
                        List<String> segments = splitnonTerminal(production);
                        //System.out.println("split" +segments);

                        // from the non terminals that are reacable from the start state we are checking two condtions
                        // 1. if that segment is a non-terminal and if that segment is already not present in the Hashset reachable non-terminals
                        // we are adding that nonterminal to the set and making change to true. so that it can check one more time until it does not change it boolean changed value. 
                        for(String segment: segments){
                            if (allNonterminals.contains(segment) && !reachableNonterminals.contains(segment)) {
                                reachableNonterminals.add(segment);
                                changed = true;
                            }
                        }

                    }
                }
            }
        } while (changed);
    
        // Identify unreachable nonterminals
        Set<String> unreachableNonterminals = new HashSet<>(allNonterminals);
        unreachableNonterminals.removeAll(reachableNonterminals);
    
        // Remove unreachable symbols from the CFG
        for (String nonterminal : unreachableNonterminals) {
            cfgMap.remove(nonterminal);
        }
    
    }
    
    // Split the production into segments enclosed within <>. This function is to get just the non-terminals from right side of production.
    private static List<String> splitnonTerminal(String production) {
        List<String> segments = new ArrayList<>();
        StringBuilder segment = new StringBuilder();
        boolean brackets = false;
    
        for (char symbol : production.toCharArray()) {
            if (symbol == '<' && !brackets) {
                brackets = true;
                segment.append(symbol);
            } else if (symbol == '>' && brackets) {
                brackets = false;
                segment.append(symbol);
                segments.add(segment.toString());
                segment.setLength(0);
            } else if (brackets) {
                segment.append(symbol);
            }
        }
    
        return segments;
    }

    // This function is to split the production values irrespective of terminals or non-terminals. It just splits them and stores them in a list.
    // This can be used in removeEps function, to find the different values possible if there nullable non-terminals.
    private static List<String> splitProduction(String production) {
        List<String> segments = new ArrayList<>();
        String segment = "";
        boolean inNonterminal = false;
    
        for (char symbol : production.toCharArray()) {
            if (symbol == '<' && !inNonterminal) {
                if (!segment.isEmpty()) {
                    segments.add(segment);
                    segment = "";
                }
                segment += symbol;
                inNonterminal = true;
            } else if (symbol == '>' && inNonterminal) {
                inNonterminal = false;
                segment += symbol;
                segments.add(segment);
                segment = "";
            } else if (symbol == ' ' && !inNonterminal) {
                if (!segment.isEmpty()) {
                    segments.add(segment);
                    segment = "";
                }
            } else {
                segment += symbol;
            }
        }
    
        // Add the final segment if it's not empty
        if (!segment.isEmpty()) {
            segments.add(segment);
        }
    
        return segments;
    }
    
    
    
    
    
}