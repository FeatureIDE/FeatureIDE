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
package de.ovgu.contracts.analysis;

import java.util.Map;

import de.ovgu.contracts.Contracts;
import de.ovgu.contracts.Defaults;
import de.ovgu.contracts.multimutation.MutationCase;

/**
 * 
 * @author Jens Meinicke
 * 
 */
public class Result {

    private final int MUTATION_CASE_SIZE;
    String analyser;
    long time;
    boolean foundError;
    private String mutationCase;
    private final Map<String, String> additions;
 
    public Result(final String analyser, final long time,
            final boolean foundError, Map<String, String> additions) {
        MUTATION_CASE_SIZE = Contracts.MUTATION_CASE_SIZE;
        this.analyser = analyser;
        this.time = time;
        this.foundError = foundError;
        this.additions = additions;
    }

    public final void setMutationCase(final MutationCase mutationCase) {
        this.mutationCase = mutationCase.toString();
    }

    @Override
    public String toString() {
        String mutationType = "MIXED";
        if (mutationCase != null) {
            if (mutationCase.contains(Defaults.TYPE_JML) && (!mutationCase.contains(Defaults.TYPE_JAVA))) {
                mutationType = Defaults.TYPE_JML;
            }
            if (mutationCase.contains(Defaults.TYPE_JAVA) && (!mutationCase.contains(Defaults.TYPE_JML))) {
                mutationType = Defaults.TYPE_JAVA;
            }
        }
        
        
        //Analyser,CaseStudy,Mutations,Time,ErrorFound
        String res = analyser + ";" + Defaults.PROJECT_NAME + ";" + MUTATION_CASE_SIZE + ";" + mutationType + ";" + mutationCase + ";" + foundError + ";" + time;
        StringBuilder adds = new StringBuilder();
 
        for (String a : additions.values()) {
            adds.append(";");
            adds.append(a);
        }
        
        
        return res + adds.toString();
//        return analyser + ";" + Contracts.MUTATION_CASE_SIZE + ";"
//                + mutationType + ";"  + mutationCase + ";"
//                + time + ";" + foundError + adds.toString();
    }

    public boolean foundError() {
        return foundError;
    }

    public Map<String, String> getAdditions() {
        return additions;
    }
}
