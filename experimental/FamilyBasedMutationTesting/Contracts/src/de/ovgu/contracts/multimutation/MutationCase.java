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

import java.util.ArrayList;
import java.util.Vector;

import de.ovgu.contracts.mutation.operators.MutationOperator;

public class MutationCase {
    public ArrayList<MutationObject> relevantObjects = new ArrayList<MutationObject>();;

    public MutationCase(Vector<Mutation> selectedMutations) {
        // identify relevant objects

        for (Mutation mut : selectedMutations) {
            MutationObject obj = mut.getObject();
            if (!relevantObjects.contains(obj)) {
                relevantObjects.add(mut.getObject());
            }
        }
        // for each relevant object perform mutations
        for (MutationObject obj : relevantObjects) {
            obj.mutate(selectedMutations, this);
        }

    }

    public String toString() {
        StringBuffer s = new StringBuffer();
        for (Mutation mut : getMutations()) {
            s.append(mut+", ");
        }
      
        return  s.substring(0, s.length()-2).replaceAll(";", "|");
    }

    public Vector<MutationOperator> getOperators() {
        Vector<MutationOperator> operators = new Vector<MutationOperator>();

        Vector<Mutation> mutations = getMutations();
        for(Mutation mut: mutations){
            operators.add(mut.getOperator());
        }
        return operators;
    }

    public Vector<Mutation> getMutations() {
        Vector<Mutation> mutations = new Vector<Mutation>();
        for (MutationObject obj : relevantObjects) {
            for (Mutation mut : obj.performedMutations.get(this)) {
                mutations.add(mut);
            }
        }
        return mutations;
    }

    public Vector<String> getMutatedFilePaths() {
        Vector<String> filepaths = new Vector<String>();
        for (MutationObject obj : relevantObjects) {
            filepaths.add(obj.getPath());
        }
        return filepaths;
    }
}
