// Name: Raghu Medarametla
// CWID: A20386265
// Course: Formal Language Theory
// Due Date: 11/14/2023
// Date of Submission: 11/14/2023
// Assignment Number: 6

import java.io.*;
import java.util.*;

//Program Class
public class p6 {
    public static void main(String[] args) {
        if (args.length != 2) {
            System.out.println("Give input file name and output file name");
            return;
        }
        //Get the input file name from the argument.
        String filename = args[0];
        //Taking this HashMap to store the context free grammar given in the input file.
        Map<String, List<String>> cfgMap = new LinkedHashMap<>();

        Set<String> terminals = new HashSet<>();

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
                    boolean inNonterminal = false;
                    String tempTString = "";
    
                    for (int i = 0; i < rightSide.length(); i++) {
                        char currentChar = rightSide.charAt(i);                    
                        if (currentChar == '<') {
                            inNonterminal = true;
                            if(!tempTString.isEmpty()){
                                terminals.add(tempTString);
                                tempTString = "";
                            }
                        }
                        else if(currentChar == '>'){
                            inNonterminal = false;
                        } 
                        else {
                            if(!inNonterminal){
                                if(currentChar!= ' '){
                                    tempTString+= currentChar;
                                }
                                if(currentChar == ' '){
                                    if(!tempTString.isEmpty()) {
                                        terminals.add(tempTString);
                                        tempTString = "";
                                    }
                                }
                            }
                        }
                    }
                    if(!tempTString.isEmpty()){
                        terminals.add(tempTString);
                    }
                }
                else {
                    rightSide = "eps";
                }
                rightSide = rightSide.replaceAll(" ", "");
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
            //System.out.println(terminals);
            //Now I am calling the three functions one by one to make a change to the given input file.
            boolean nullstart = removeEps(cfgMap,startSymbol);
            removeUnproductive(cfgMap);
            removeUnreachable(cfgMap,startSymbol);

            //System.out.println(cfgMap);

            //I am doing three functions first removing the unit prodctions
            removeUnitProductions(cfgMap);
            //After removing the unit productions, I am doing the immediate left recursive.
            Map<String, List<String>> newCfgMap = removeImmediateLeftRecursion(cfgMap);
            // After that I am working on removing the left recursive from the CFG grammar.
            removeLeftRecursion(newCfgMap,cfgMap);
            // Again I am calling the function to check again if there are any unit productions
            removeUnitProductions(newCfgMap);

            removeMixed(newCfgMap, terminals);
            convertToGreibach(newCfgMap,cfgMap,terminals);
            removeUnreachable(newCfgMap, startSymbol);


            if(nullstart == true){
                List<String> newprod = new ArrayList<String>();
                newprod.add("eps");
                newprod.add(startSymbol);
                newCfgMap.put("S*", newprod);

            }
            //System.out.println(newCfgMap);


            String outputFileName = args[1];

            try (PrintWriter writer = new PrintWriter(outputFileName)) {
                //Write the start symbol components if they exist
                if (newCfgMap.containsKey("S*")) {
                    List<String> startSymbolProductions = newCfgMap.get("S*");
                    for (String production : startSymbolProductions) {
                        if (production.equals("eps")) {
                            writer.println("<" + "S*" + "> ::=");
                        } else {
                            writer.println("<" + "S*" + "> ::= " + production);
                        }
                    }
                }
                
                for (String nonterm : newCfgMap.keySet()) {
                    if (!nonterm.equals("S*")) {
                        List<String> productions = newCfgMap.get(nonterm);
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


    private static void convertToGreibach(Map<String, List<String>> newCfgMap, Map<String, List<String>> cfgMap, Set<String> terminals) {

        // Here I am taking the linear order from the linearorder function, Then I am taking working backwards from last to first in the original non-terminals that were present and making sure
        // each non terminal right production starts with terminal, if is not starting with the terminal then I am substituting the specific non-terminals to the productions.
        Map<String, Integer> nonterminalOrder = linearOrder(cfgMap);

        List<String> nonterminals = new ArrayList<>(nonterminalOrder.keySet());
        Collections.reverse(nonterminals);

        for(String nonterminal: nonterminals){
            List<String> productions = newCfgMap.get(nonterminal);

            Boolean change = false;
            // This while loop continues until the no production have any terminals starting with.
            while(true){
                change = false;
                List<String> newProdList = new ArrayList<>();
                Set<String> removeList = new HashSet<>();
            
                for(int i=0;i<productions.size();i++){
                    String prod = productions.get(i);
                    if(terminals.contains(prod) || prod.charAt(0)!='<'){
                        continue;
                    }
                    List<String> segments = splitProduction(prod);
                    String firstSegment = segments.get(0);
                    removeList.add(prod);
                    List<String> rightprodStrings= newCfgMap.get(firstSegment); 
                    for(String rightprodString: rightprodStrings){
                        newProdList.add(rightprodString+prod.substring(firstSegment.length()));
                    
                    }
                }
                for(String remove: removeList){
                    if(productions.contains(remove)){
                    productions.remove(remove);
                    }
                }
                for(String add: newProdList){
                    if(!productions.contains(add) && !nonterminal.equalsIgnoreCase(add)){
                        productions.add(add);
                    }
                }
                if(!change){
                    break;
                }
            }
            newCfgMap.put(nonterminal, productions);
        }

        List<String> newNonT = new ArrayList<>(newCfgMap.keySet());

        for(String nonterminal: newNonT){
            if(nonterminals.contains(nonterminal)){
                continue;
            }
            List<String> productions = newCfgMap.get(nonterminal);

            Boolean change = false;
            // This while loop continues until the no production have any terminals starting with.
            while(true){
                change = false;
                List<String> newProdList = new ArrayList<>();
                Set<String> removeList = new HashSet<>();
            
                for(int i=0;i<productions.size();i++){
                    String prod = productions.get(i);
                    if(terminals.contains(prod) || prod.charAt(0)!='<'){
                        continue;
                    }
                    List<String> segments = splitProduction(prod);
                    String firstSegment = segments.get(0);
                    removeList.add(prod);
                    List<String> rightprodStrings= newCfgMap.get(firstSegment); 
                    for(String rightprodString: rightprodStrings){
                        newProdList.add(rightprodString+prod.substring(firstSegment.length()));
                    
                    }
                }
                for(String remove: removeList){
                    if(productions.contains(remove)){
                    productions.remove(remove);
                    }
                }
                for(String add: newProdList){
                    if(!productions.contains(add) && !nonterminal.equalsIgnoreCase(add)){
                        productions.add(add);
                    }
                }
                if(!change){
                    break;
                }
            }
            newCfgMap.put(nonterminal, productions);
        }

    }


    private static void removeMixed(Map<String, List<String>> newCfgMap, Set<String> terminals) {
        Map<String, List<String>> updatedCfgMap = new LinkedHashMap<>(newCfgMap);

        for (String nonterminal : updatedCfgMap.keySet()) {
            List<String> productions = updatedCfgMap.get(nonterminal);

            for (int i = 0; i < productions.size(); i++) {
                String production = productions.get(i);
                String newString = "";
                String tempString = "";
                boolean nonTerminalcheck = false;
                if(terminals.contains(production)){
                    continue;
                }
                
                for(int j=0;j<production.length();j++){
                    if(production.charAt(j) == '<'){
                        newString += production.charAt(j);
                        nonTerminalcheck = true;
                    }
                    else if(production.charAt(j) == '>'){
                        newString += production.charAt(j);
                        nonTerminalcheck = false;
                    }
                    else{
                        if(!nonTerminalcheck){
                            tempString += production.charAt(j);

                            if(terminals.contains(tempString)){
                                newString+= "<T" + tempString + ">";
                                tempString = "";
                            }
                        }
                        else{
                            newString += production.charAt(j);
                        }
                    }

                }
                productions.set(i, newString);
            }
        }

        for (String terminal : terminals) {
            String newNonterminal = "<T" + terminal + ">";
            updatedCfgMap.put(newNonterminal, Arrays.asList(terminal));
        }


        newCfgMap.clear();
        newCfgMap.putAll(updatedCfgMap);

    }


    // This function is to remove epsilons from the context free grammaer
    private static boolean removeEps(Map<String, List<String>> cfgMap, String startSymbol) {

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

        boolean nullablestart = false;
        if(nullableSet.contains(startSymbol)){
            nullablestart = true;

            // List<String> newprod = new ArrayList<String>();
            // newprod.add("eps");
            // newprod.add(startSymbol);
            // cfgMap.put("S*", newprod);
        }
        return nullablestart;

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
    private static Map<String, Integer> linearOrder(Map<String, List<String>> cfgMap){
        // First I get the non-terminals from the old cfg map.
        List<String> nonterminals = new ArrayList<>(cfgMap.keySet());

        // I create a new Hashmap that keeps the count of occurance of non-terminal order
        Map<String, Integer> nonterminalCount = new LinkedHashMap<>();
        for (int i = 0; i < nonterminals.size(); i++) {
            nonterminalCount.put(nonterminals.get(i), i);
        }
        return nonterminalCount;

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
                        newProdList.add(rightprodString+production.substring(firstSegment.length()));
                        
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
