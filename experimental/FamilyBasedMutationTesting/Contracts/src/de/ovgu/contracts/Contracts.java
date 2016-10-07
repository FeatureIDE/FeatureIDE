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
package de.ovgu.contracts;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import javax.annotation.CheckForNull;

import de.ovgu.contracts.analysis.AbstractAnalyser;
import de.ovgu.contracts.analysis.JavaPathfinder;
import de.ovgu.contracts.analysis.MonKeY;
import de.ovgu.contracts.analysis.Result;
import de.ovgu.contracts.analysis.ResultsExporter;
import de.ovgu.contracts.builder.FeatureHouseBuilder;
import de.ovgu.contracts.builder.compiler.AbstractCompiler;
import de.ovgu.contracts.builder.compiler.RACompiler;
import de.ovgu.contracts.multimutation.MultiMutator;
import de.ovgu.contracts.multimutation.Mutation;
import de.ovgu.contracts.multimutation.MutationCase;
import de.ovgu.contracts.multimutation.MutationObject;
import de.ovgu.contracts.utils.FileManager;
import de.ovgu.contracts.utils.Writer;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * The main class. Mutates a features and anlalyzes the resulting metaproduct
 * with KeY and JPF.
 * 
 * @author Jens Meinicke
 */
public final class Contracts implements Defaults {

//    private static final AbstractCompiler COMPILER = new JavaCompiler();
    private static final AbstractCompiler COMPILER = new RACompiler();
    private static final AbstractAnalyser KEY = new MonKeY();
    private static final AbstractAnalyser JPF = new JavaPathfinder();

    private static final File SOURCE = new File(FEATURE_PATH);
    private final List<Result> jpfResults = new LinkedList<Result>();
    private final List<Result> keyResults = new LinkedList<Result>();
    private final List<Result> combinedResults = new LinkedList<Result>();
    private static final String KEY_RESULTS_PATH = "\\key";
    private static final String JPF_RESULTS_PATH = "\\jpf";
    private static final String COMBINED_RESULTS_PATH = "\\combined";

    public static int MUTATION_CASE_SIZE;

    private final String FEATUREMODEL_PATH;
    private final FeatureHouseBuilder BUILDER;
    private final ResultsExporter RESULTS_EXPORTER = new ResultsExporter();
    public static MutationType MUTATION_TYPE = MutationType.ALL;

    private Contracts(final int min, final int max, final int size) {
        FEATUREMODEL_PATH = CASE_STUDY_PATH + "model_" + size + ".xml";
        BUILDER = new FeatureHouseBuilder(NEW_FEATURE_PATH, CONFIG_PATH, FEATUREMODEL_PATH, SRC_PATH);
        try {
            FeatureModel featureModel = new FeatureModel();
            XmlFeatureModelReader reader = new XmlFeatureModelReader(featureModel);
            reader.readFromFile(new File(FEATUREMODEL_PATH));
            
            FileManager.removeFiles(new File(TMP_PATH));
            FileManager.createFolder(BIN_PATH);
            
            for (int j = min; j <= max; j++) {
                Contracts.MUTATION_CASE_SIZE = j;
                if (j == 0) {
                    for (int i = 0; i < MUTATION_CASE_AMOUNT; i++) {
                        boolean firstRunValid = analyze(null); // gets the results for no mutation
                        if (!firstRunValid) {
                            return;
                        }
                    }
                    continue;
                }
                
                FileManager.copyFiles(SOURCE, NEW_FEATURE_PATH);
                final MultiMutator mutator = new MultiMutator(NEW_FEATURE_PATH, featureModel);
                int i = 1;
                List<MutationCase> mutations = mutator.mutate(MUTATION_CASE_SIZE, MUTATION_CASE_AMOUNT);
                for (final MutationCase mutationCase : mutations) {
                    System.out.println("---------------------------------------------------");
                    System.out.println("");
                    System.out.println(i++ + " / " + mutations.size() + " mutations");
                    System.out.println("#Mutations: " + MUTATION_CASE_SIZE);
                    System.out.println("ModelSize: " + size);
                    for (Mutation m : mutationCase.getMutations()) {
                        System.out.println(m);
                    }
                    System.out.println("");
                    System.out.println("---------------------------------------------------");
                    analyze(mutationCase);
                    
                }
            }
            long time = System.currentTimeMillis() / 1000;
            RESULTS_EXPORTER.printResults(RESULTS_PATH + "size" + size + "_" + MUTATION_TYPE + "_" + time + JPF_RESULTS_PATH + ".csv", jpfResults);
            RESULTS_EXPORTER.printResults(RESULTS_PATH + "size" + size + "_" + MUTATION_TYPE + "_" + time + KEY_RESULTS_PATH + ".csv", keyResults);
            RESULTS_EXPORTER.printResults(RESULTS_PATH + "size" + size + "_" + MUTATION_TYPE + "_" + time + COMBINED_RESULTS_PATH + ".csv", combinedResults);
        } catch (FileNotFoundException | UnsupportedModelException e) {
            e.printStackTrace();
        } finally {
            // remove all temp files
            FileManager.removeFiles(new File(TMP_PATH));
        }
    }

    private boolean analyze(@CheckForNull final MutationCase mutationCase) {
        try {
            FileManager.copyFiles(SOURCE, NEW_FEATURE_PATH);
            if (mutationCase != null) {
                for (MutationObject obj : mutationCase.relevantObjects) {
                    Writer.setFileContent(obj.getPath(), obj.mutatedContent.get(mutationCase));
                }
            }
    
            // build metaproduct for Model Checking
            BUILDER.build(IFeatureProject.META_MODEL_CHECKING_BDD_JAVA_JML);
    //        BUILDER.build(IFeatureProject.META_MODEL_CHECKING);
            COMPILER.compile(SRC_PATH, BIN_PATH);
            // run JavaPathfinder
            final Result jpfResult = JPF.runRounds();
            synchronized (this) {
                wait(100);
                // hopefully clears cache
            }
            jpfResults.add(jpfResult);
            if (mutationCase != null) {
                jpfResult.setMutationCase(mutationCase);
            } else {
                if (jpfResult.foundError()) {
                    System.err.println("Non mutated case study not verified");
                    return false;
                }
            }
    
            // build metaproduct for Theorem Proving
            BUILDER.build(IFeatureProject.META_THEOREM_PROVING);
            // run KEY
            final Result keyResult = KEY.runRounds();
            synchronized (this) {
                wait(100);
                // hopefully clears cache
            }
            keyResults.add(keyResult);
            if (mutationCase != null) {
                keyResult.setMutationCase(mutationCase);
            } else {
                if (keyResult.foundError()) {
                    System.err.println("Non mutated case study not proven");
                    return false;
                }
            }
            
            // Save results for synergies
            final Map<String, String> adds = new HashMap<>();
            adds.put("KeY Result", keyResult.foundError() + "");
            adds.put("JPF Result", jpfResult.foundError() + "");
            String syn = "";
            if (!(keyResult.foundError() && jpfResult.foundError())) {
                if (keyResult.foundError()) {
                    syn = "KEY";
                    adds.put("KEYSyn", "true");
                    adds.put("JPFSyn", "false");
                } else if (jpfResult.foundError()) {
                    syn = "JPF";
                    adds.put("JPFSyn", "true");
                    adds.put("KEYSyn", "false");
                } else {
                    adds.put("JPFSyn", "false");
                    adds.put("KEYSyn", "false");
                }
            } else {
                adds.put("JPFSyn", "false");
                adds.put("KEYSyn", "false");
            }
            adds.put("Synergy", syn);
            final Result combinedResult = new Result("Combined", 0, keyResult.foundError() || jpfResult.foundError(), adds);
            if (mutationCase != null) {
                combinedResult.setMutationCase(mutationCase);
            }
            combinedResults.add(combinedResult);
        } catch (InterruptedException e) {
            e.printStackTrace();
        } finally {
            FileManager.removeFiles(NEW_FEATURE_PATH);
        }
        return true;
    }

    public static void main(final String[] args) {
        long time = System.currentTimeMillis();
        for (int size = 1; size <= 10; size+=1) {
            for (final MutationType mt : MutationType.values()) {
                MUTATION_TYPE = MutationType.ALL;
                new Contracts(0, 10, size);
            }
        }
        time = System.currentTimeMillis() - time;
        long seconds = (time / 1000);
        long minutes = (seconds / 60);
        long hours   = minutes / 60;
        System.out.println("complete duration rounds:");
        System.out.println(hours   + "h " + minutes%60 + "m " + seconds%60 + "s");
    }

}
