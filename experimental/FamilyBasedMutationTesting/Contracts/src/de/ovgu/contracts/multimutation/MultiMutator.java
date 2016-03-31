/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.contracts.multimutation;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Random;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.ovgu.contracts.Contracts;
import de.ovgu.contracts.Defaults.MutationType;
import de.ovgu.contracts.mutation.operators.MutationOperator;
import de.ovgu.contracts.utils.FileManager;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Mutates all files from a folder. Each possible mutation depending on the
 * source files and mutation operators is created once (by calling
 * getMutations()).
 * 
 * @author Fabian Benduhn
 * 
 */
public class MultiMutator {

    private static final String SINGLE_LINE_JML_PATTERN = "//@.*\n{0,1}?";
    static final String MULTI_LINE_JML_PATTERN = "(?s)/\\*@(?:(?!@\\*).)+@?\\*/";
    private static final String ALL_PATTERN = ".*";
    /**
     * File extensions to be considered for mutations.
     */
    private static final String[] EXTENSIONS = new String[] { "java" };
    /**
     * MutationOperators to be used.
     */
    private static final MutationOperator[] OPERATORS = {
            new MutationOperator(" <= ", " >= "),
            new MutationOperator(" >= ", " <= "),

            new MutationOperator(" != ", " == "),
            new MutationOperator(" == ", " != "),
            
            new MutationOperator(" ==> ", " <==>"),
            new MutationOperator(" <==> ", "  ==> "),

            new MutationOperator(" < ", " > "),
            new MutationOperator(" > ", " < "),

            new MutationOperator(" && ", " || "),
            new MutationOperator(" \\|\\| ", " && "),

            new MutationOperator(" << ", " >> "),
            new MutationOperator(" >> ", " << "), 
            
            new MutationOperator(" \\+ "," - "),
            new MutationOperator(" - "," + "),
            
            new MutationOperator(" \\+= "," -= "),
            new MutationOperator(" -= "," += "),
            
            new MutationOperator(" \\* "," / "),
            new MutationOperator(" \\/ "," * "),
            
            new MutationOperator(" false "," true "),
            new MutationOperator(" true "," false "),
         
            new MutationOperator(" false;"," true; "),
            new MutationOperator(" true;"," false;")
    
            };
    
    private static final long SEED = 45;
    private long seedCount=0;
    /**
     * List of MutationObjects. Each MutationObject represents a file that
     * should be mutated.
     */
    public final ArrayList<MutationObject> objectList = new ArrayList<MutationObject>();

    HashMap<MutationObject, ArrayList<Mutation>> objects = new HashMap<MutationObject, ArrayList<Mutation>>();
    public Vector<Mutation> mutations = new Vector<Mutation>();

    public MultiMutator(final String path, final FeatureModel featureModel) {
        final List<String> features = featureModel.getConcreteFeatureNames();
        for (final File file : FileManager.listAll(new File(path), false)) {
            if (file.isDirectory() && features.contains(file.getName())) {
                initMutationObjects(file);
            }
        }
        mutateAll(Contracts.MUTATION_TYPE);
    }

    /**
     * Creates a MutationObject for each file with the specified extension
     * inside directory dir (including sub-directories)
     * 
     * @param dir
     *            File object representing the directory to be considered.
     */
    private void initMutationObjects(final File dir) {
        final List<File> files = FileManager.listFiles(dir, EXTENSIONS, true);
        for (final File file : files) {
            MutationObject obj = new MutationObject(file.getAbsolutePath());
            objectList.add(obj);
            objects.put(obj, new ArrayList<Mutation>());

        }

    }

    /**
     * 
     * @param type
     * @return number of applied mutations
     */
    private void mutateAll(final MutationType type) {
        for (MutationObject obj : objectList) {
            for (MutationOperator op : OPERATORS) {
                if (type != MutationType.JAVA_ONLY) {
                    //adding jml mutations
                    for (Integer index : getIndices(obj, op,
                            MutationType.JML_ONLY)) {
                        Mutation mut = new Mutation(obj, op, index,
                                MutationType.JML_ONLY);
                        objects.get(obj).add(mut);
                        mutations.add(mut);
                      }
                }

                if (type != MutationType.JML_ONLY) {
                    //adding java mutations
                    for (Integer index : getIndices(obj, op,
                            MutationType.JAVA_ONLY)) {
                        Mutation mut = new Mutation(obj, op, index,
                                MutationType.JAVA_ONLY);
                        objects.get(obj).add(mut);
                        mutations.add(mut);
                    }
                }
            }
        }

    }

    /**
     * Returns a list of indices of possible mutations. Each index represents an
     * occurance of the source pattern defined by the mutation operator.
     * 
     * @param object
     * @param operator
     * @return
     */
    List<Integer> getIndices(MutationObject object, MutationOperator operator,
            MutationType type) {
        List<Integer> resultList;
        List<Integer> singleLineList;
        List<Integer> multiLineList;
        switch (type) {
        case ALL:
            resultList = doMatching(object.getOriginalContent(), operator, ALL_PATTERN);
            break;

        case JML_ONLY:
            singleLineList = doMatching(object.getOriginalContent(), operator,
                    SINGLE_LINE_JML_PATTERN);
            multiLineList = doMatching(object.getOriginalContent(), operator, MULTI_LINE_JML_PATTERN);
            resultList = new ArrayList<Integer>(singleLineList);
            resultList.addAll(multiLineList);
            break;

        case JAVA_ONLY:
            singleLineList = doMatching(object.getOriginalContent(), operator,
                    SINGLE_LINE_JML_PATTERN);
            multiLineList = doMatching(object.getOriginalContent(), operator, MULTI_LINE_JML_PATTERN);
            resultList = doMatching(object.getOriginalContent(), operator, ALL_PATTERN);
            resultList.removeAll(singleLineList);
            resultList.removeAll(multiLineList);
            break;
        default:
            resultList = new ArrayList<Integer>();
            System.out.println("Invalid MutationType");
            break;
        }
        return resultList;
    }

    static List<Integer> doMatching(String content,
            MutationOperator operator, String pattern) {
        List<Integer> resultList = new ArrayList<Integer>();
        Pattern outerRegex = Pattern.compile(pattern);
        Pattern innerRegex = Pattern.compile(operator.getSourcePattern());
        Matcher outerMatcher = outerRegex.matcher(content);
        Matcher innerMatcher = innerRegex.matcher(content);
        while (outerMatcher.find()) {
            innerMatcher.region(outerMatcher.start(), outerMatcher.end());
            while (innerMatcher.find()) {

                resultList.add(innerMatcher.start());
            }
        }
        return resultList;
    }

    private ArrayList<MutationCase> mutationCases = new ArrayList<MutationCase>();


    /**
     * selects a random subset of mutations of a given size and creates a new
     * mutationCase for
     * 
     * @param size
     * @return
     */
    private void addRandomMutationCase(int size) {
        Vector<Mutation> selectedMutations = selectRandomMutations(size);
        mutationCases.add(new MutationCase(selectedMutations));
    }

    private Vector<Mutation> selectRandomMutations(int mutation_size) {
        Vector<Mutation> selectedMutations = new Vector<Mutation>();
        selectedMutations.addAll(mutations);
        Collections.shuffle(selectedMutations, new Random(SEED+seedCount++));
        selectedMutations.setSize(mutation_size);
        return selectedMutations;
    }

    /**
     * randomly performs iter x size mutations
     * 
     * @param size
     *            number of mutations for each mutation case.
     * @param iter
     *            number of mutation cases to be performed
     * @return
     */
    public ArrayList<MutationCase> mutate(int size, int iter) {
        mutationCases.clear();
        if (size > mutations.size())
            throw new RuntimeException("Cannot select " + size
                    + " mutations from " + mutations.size() + " mutations.");

        for (int i = 0; i < iter; i++) {
            addRandomMutationCase(size);
        }

        return mutationCases;
    }

    /**
     * randomly performs all x size mutations, number of mutation cases = number
     * of possible mutations
     * 
     * @param size
     *            number of mutations for each mutation case.
     * 
     * @return
     */
    public ArrayList<MutationCase> mutate(int size) {
        return mutate(size, mutations.size());
    }

    /**
     * performs all single mutations
     * 
     * @param size
     *            number of mutations for each mutation case.
     * 
     * @return
     */
    public ArrayList<MutationCase> mutate() {
        mutationCases.clear();
        for (Mutation mut : mutations) {
            Vector<Mutation> mutVec = new Vector<Mutation>();
            mutVec.add(mut);
            mutationCases.add(new MutationCase(mutVec));
        }

        return mutationCases;
    }

}
