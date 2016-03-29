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
package de.ovgu.contracts.mutation.operators;
/**
 * 
 * @author Fabian Benduhn
 * 
 */
public class MutationOperator {

    String sourcePattern;
    String targetPattern;

    /**
     * Creates a MutationOperator that replaces each occurance of the source pattern with target string. 
     * @param source regex pattern for source
     * @param target
     */
    public MutationOperator(String source, String target) {
        sourcePattern = source;
        targetPattern = target;
    }


    public String getSourcePattern() {
        return sourcePattern;
    };

    public String getTargetPattern() {
        return targetPattern;
    };

    public String toString() {
        return "{" + getSourcePattern() + "} --> {" + getTargetPattern() + "}";
    }


}
