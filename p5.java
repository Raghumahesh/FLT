// Name: Raghu Medarametla
// CWID: A20386265
// Course: Formal Language Theory
// Due Date: 11/2/2023
// Date of Submission: 11/2/2023
// Assignment Number: 5


import java.io.*;
import java.util.*;

//Program Class
public class p5 {
    public static void main(String[] args) {

        // I am checking the arguments to pass
        if (args.length != 2) {
            System.out.println("Give input file name and output file name");
            return;
        }
        //Get the input file name from the argument.
        String filename = args[0];
        //Taking this HashMap to store the context free grammar given in the input file.
        Map<String, List<String>> cfgMap = new LinkedHashMap<>();

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
                leftSide = leftSide.replaceAll(" ", "");
                String rightSide;
                
                //If right is empty then I am making it is as eps.
                if (parts.length > 1) {
                    rightSide = parts[1].trim();
                    rightSide = rightSide.replaceAll(" ", "");
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
            //I am doing three functions first removing the unit prodctions
            removeUnitProductions(cfgMap);
            //After removing the unit productions, I am doing the immediate left recursive.
            Map<String, List<String>> newCfgMap = removeImmediateLeftRecursion(cfgMap);
            //removeUnitProductions(newCfgMap);
            // After that I am working on removing the left recursive from the CFG grammar.
            removeLeftRecursion(newCfgMap,cfgMap);
            //System.out.println(newCfgMap);
            // Again I am calling the function to check again if there are any unit productions
            removeUnitProductions(newCfgMap);
            //System.out.println(newCfgMap);

            String outputFileName = args[1];

            // Here I am printing the output to the file based on the given syntax.
            try (PrintWriter writer = new PrintWriter(new FileWriter(outputFileName))) {
                for (Map.Entry<String, List<String>> entry : newCfgMap.entrySet()) {
                    String nonterminale = entry.getKey();
                    List<String> productions = entry.getValue();
    
                    for (String production : productions) {
                        writer.println(nonterminale + " ::= " + production);
                    }

                }
            } catch (IOException e) {
                System.out.println("Error when writing to the output file");
            }

        } catch (IOException e) {
            System.out.println("Error Reading the file");
        }
    }

    // Function to remove unit productions.
    private static void removeUnitProductions(Map<String, List<String>> updatedCfgMap) {

        // I am taking a copy of the cfgmap so that I can make changes to this code.
        //Map<String, List<String>> updatedCfgMap = new LinkedHashMap<>(cfgMap);

        boolean unitExist = true;

        // This loop will continue until there are any unit productions present. If there are no more then I am coming out of loop.
        while (unitExist) {
            unitExist = false;
            // looping over all the non-terminals that are present in the grammar.
            for (String nonterminal : updatedCfgMap.keySet()) {
                List<String> productions = updatedCfgMap.get(nonterminal);

                // This list to store the unit productions whenever we came across.
                List<String> unitProductions = new ArrayList<>();
                // If the production of right side is only contains one nonterminal then it should be added to the unitporductions list.
                for (String production : productions) {

                    String production1=production.trim();
                    //System.out.println(production);
                    if (production1.startsWith("<") && production1.endsWith(">") 
                            && production1.indexOf("<") == production1.lastIndexOf("<")) {
                        unitProductions.add(production);

                    }
                }
                //List<String> templist = updatedCfgMap.get(nonterminal);
                for(String sd: unitProductions){
                    //System.out.println("cdsout: " + sd);
                    if(productions.contains(sd)){
                        productions.remove(sd);
                        //System.out.println("cds: " + sd);
                    }
                }
                //templist.removeAll(unitProductions);
                updatedCfgMap.put(nonterminal, productions);
                // updatedCfgMap.get(nonterminal).removeAll(unitProductions);

                //System.out.println(updatedCfgMap);

                // Here getting the production of each unit symbol so that we can substitue that in updatedcfg
                for (String unitProduction : unitProductions) {
                    String unitSymbol = unitProduction;
    
                    List<String> derivedProductions = new ArrayList<String>();
                    derivedProductions = updatedCfgMap.containsKey(unitSymbol) ? updatedCfgMap.get(unitSymbol) : new ArrayList<String>();

                    for (String derivedProduction : derivedProductions) {
                        if (!productions.contains(derivedProduction)) {
                            updatedCfgMap.get(nonterminal).add(derivedProduction);
                            unitExist = true;
                        }
                    }
                }
                
            }
    
        }


    }

    // Function to remove the left recursive grammar
    private static void removeLeftRecursion(Map<String, List<String>> newCfgMap, Map<String, List<String>> cfgMap ) {

        // First I get the non-terminals from the old cfg map.
        List<String> nonterminals = new ArrayList<>(cfgMap.keySet());

        // I create a new Hashmap that keeps the count of occurance of non-terminal order
        Map<String, Integer> nonterminalCount = new LinkedHashMap<>();
        for (int i = 0; i < nonterminals.size(); i++) {
            nonterminalCount.put(nonterminals.get(i), i);
        }
        //After I fixed an order for the non-terminals
        // I intialize the left order and right order.
        int leftOrder=0, rightOrder=0;
        // Loop through each non-terminal and taking the productions of non-terminal.
        for (String nonterminal : nonterminals) {
            List<String> nonterminalProductions = newCfgMap.get(nonterminal);

            Boolean change = false;
            // This while loop continues until the no production have any left recusrive function like left order> right order
            while(true){
                change = false;

                // I create a new productionlist and removelist
                List<String> newProdList = new ArrayList<>();
                Set<String> removeList = new HashSet<>();
                // Now, I will the left side non-terminal's number from nonterminal order and in the same way 
                // I get the right side terminal's number by checking if the first symbol in right side is a non-terminal first
                // and ten compare the both numbers.
                for (int i = 0; i < nonterminalProductions.size(); i++) {
                    String production = nonterminalProductions.get(i);
                    List<String> segments = splitProduction(production);
                    String firstSegment = segments.get(0);
                    if(firstSegment.startsWith("<") && firstSegment.endsWith(">")){
                        rightOrder = nonterminalCount.get(firstSegment);
                    }
                    //if not continue
                    else{
                        continue;
                    }
                    if (nonterminalCount.containsKey(nonterminal)) {
                        leftOrder = nonterminalCount.get(nonterminal);

                    }
                    if(leftOrder<=rightOrder){
                        continue;
                    }
                    // Here we add to the production the replacing non-terminal with its own productions form a new prodlist and also add removing right side producutions in the removelist
                    change = true;
                    removeList.add(production);
                    List<String> rightprodStrings= newCfgMap.get(firstSegment); 
                    for(String rightprodString: rightprodStrings){
                        newProdList.add(rightprodString+production.substring(nonterminal.length()));
                        
                    }
                    //System.out.println(newProdList);               
                }
                // After I remove the removelist from the nonterminal productuions
                for(String remove: removeList){
                    if(nonterminalProductions.contains(remove)){
                    nonterminalProductions.remove(remove);
                    }
                }
                // Then adding the newprodlist to nonterminal productions
                for(String add: newProdList){
                    if(!nonterminalProductions.contains(add) && !nonterminal.equalsIgnoreCase(add)){
                        nonterminalProductions.add(add);
                    }
                }
                if(!change){
                    break;
                }
            }
            newCfgMap.put(nonterminal, nonterminalProductions);
            removeImmediateLeftRecursionforNonterminal(newCfgMap,nonterminal);
            //System.out.println(newCfgMap);


        }

    }


    private static void removeImmediateLeftRecursionforNonterminal(Map<String, List<String>> newCfgMap, String nonterminal) {

        List<String> productions = newCfgMap.get(nonterminal);
        List<String> newProductions = new ArrayList<>();
        newCfgMap.put(nonterminal, new ArrayList<>());
        List<String> leftRecursive = new ArrayList<>();
    
        // Separate left-recursive and non-left-recursive productions
        for (String production : productions) {
            if (production.startsWith(nonterminal)) {
                leftRecursive.add(production.substring(nonterminal.length()));
            } else {
                newProductions.add(production);
            }
        }
    
        if (!leftRecursive.isEmpty()) {
            String newNonterminal = "<" + nonterminal.substring(1,nonterminal.length()-1) + "'>";
            while(newCfgMap.containsKey(newNonterminal)){
                newNonterminal = "<" + newNonterminal.substring(1,newNonterminal.length()-1) + "'>";
            }
            newCfgMap.put(newNonterminal, new ArrayList<>());
    
            // Create non-left-recursive productions
            for (String production : newProductions) {
                newCfgMap.get(nonterminal).add(production);
                newCfgMap.get(nonterminal).add(production + "" + newNonterminal);
            }
    
            for (String production : leftRecursive) {
                newCfgMap.get(newNonterminal).add(production);

                newCfgMap.get(newNonterminal).add(production + "" + newNonterminal);
            }
        } else {
            newCfgMap.put(nonterminal, newProductions);
        }

    }

    //Function to remove the immediate left grammar.
    private static Map<String, List<String>> removeImmediateLeftRecursion(Map<String, List<String>> cfgMap) {
        Map<String, List<String>> newCfgMap = new LinkedHashMap<>();
    
        // First I am taking two sets to seperate the total productions of the respective non-terminal into 
        // newproductions and left recursive terminals
        for (String nonterminal : cfgMap.keySet()) {
            List<String> productions = cfgMap.get(nonterminal);
            List<String> newProductions = new ArrayList<>();
            newCfgMap.put(nonterminal, new ArrayList<>());
            List<String> leftRecursive = new ArrayList<>();
    
            // Separate left-recursive and non-left-recursive productions
            for (String production : productions) {
                if (production.startsWith(nonterminal)) {
                    leftRecursive.add(production.substring(nonterminal.length())); 
                } else {
                    newProductions.add(production); 
                }
            }
            // If left recursive is not empty then, I am creating a new terminal. 
            if (!leftRecursive.isEmpty()) {
                String newNonterminal = "<" + nonterminal.substring(1,nonterminal.length()-1) + "'" + ">";
                while(newCfgMap.containsKey(newNonterminal)){
                    newNonterminal = "<" + newNonterminal.substring(1,newNonterminal.length()-1) + "'>";
                }
                newCfgMap.put(newNonterminal, new ArrayList<>());
    
                // Create non-left-recursive productions
                for (String production : newProductions) {
                    newCfgMap.get(nonterminal).add(production);
                    newCfgMap.get(nonterminal).add(production + " " + newNonterminal);
                }
    
                for (String production : leftRecursive) {
                    newCfgMap.get(newNonterminal).add(production);
                    newCfgMap.get(newNonterminal).add(production + " " +newNonterminal);
                }
            } 
            else {
                newCfgMap.put(nonterminal, newProductions);
            }
        }
    
        return newCfgMap;
    }
    
    



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