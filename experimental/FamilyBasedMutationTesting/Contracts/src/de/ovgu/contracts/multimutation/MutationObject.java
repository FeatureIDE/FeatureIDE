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

import java.util.HashMap;
import java.util.Vector;

import de.ovgu.contracts.utils.Reader;

/**
 * Represents an object that can be mutated.
 * 
 * @author Fabian Benduhn
 * 
 */

public class MutationObject {
    public String originalContent;
    public HashMap<MutationCase, String> mutatedContent = new HashMap<MutationCase, String>();
    public String filepath;
    public HashMap<MutationCase, Vector<Mutation>> performedMutations = new HashMap<MutationCase, Vector<Mutation>>();

    public MutationObject(String path) {
        this.filepath = path;
        this.originalContent = new Reader().getFileContent(filepath);

    }

    public String getOriginalContent() {
        return originalContent;
    }

    public String getPath() {
        return filepath;
    }

    public String toString() {
        return filepath;
    }

    /**
     * performs all mutations that belong to this object, others are ignored.
     * 
     * @param selectedMutations
     * @param mutationCase
     * @return
     */
    public String mutate(Vector<Mutation> selectedMutations,
            MutationCase mutationCase) {
        if (!mutatedContent.containsKey(mutationCase))
            mutatedContent.put(mutationCase, originalContent);
        if (!performedMutations.containsKey(mutationCase))
            performedMutations.put(mutationCase, new Vector<Mutation>());
        String content = mutatedContent.get(mutationCase);
        for (Mutation mut : selectedMutations) {
            if (mut.getObject().equals(this)) {
                String newContent = getMutatedContent(
                        mutatedContent.get(mutationCase), mut);
                mutatedContent.remove(mutationCase);
                mutatedContent.put(mutationCase, newContent);
                performedMutations.get(mutationCase).add(mut);
            }
        }
        return content;
    }

    /**
     * Returns the mutated content that belongs to this mutation. The actual
     * mutation takes places here (lazy).
     */
    private String getMutatedContent(String content, Mutation mut) {
        String mutatedContent;

        mutatedContent = content.substring(0, mut.index)
                + mut.op.getTargetPattern()
                + content.substring(mut.index
                        + mut.op.getTargetPattern().length());

        return mutatedContent;
    }
}
