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




import de.ovgu.contracts.Defaults;
import de.ovgu.contracts.Defaults.MutationType;
import de.ovgu.contracts.mutation.operators.MutationOperator;
import de.ovgu.contracts.utils.Reader;

/**
 * Represents a single mutation, specified by a mutation object, mutation
 * operator and the index of mutation within the file content string.
 * 
 * @author Fabian Benduhn
 * 
 */
public class Mutation {
    MutationObject obj;
    MutationOperator op;
    int index;
    MutationType type;
    
    public Mutation(MutationObject obj, MutationOperator op, int index, MutationType type) {
        this.obj = obj;
        this.op = op;
        this.index = index;
        this.type = type;
    }
    
    public MutationType getType() {
        return type;
    }

    public String toString() {
                
        return "[" + obj + "," + op
                + Reader.getLineString(obj.originalContent, index) +", "+(type==MutationType.JAVA_ONLY ? Defaults.TYPE_JAVA : Defaults.TYPE_JML)+ "]";
    }

    public File getMutatedFile() {

        return new File(obj.getPath());
    }

    public MutationOperator getOperator() {
        return op;
    }

    public MutationObject getObject() {
        return obj;
    }
}
