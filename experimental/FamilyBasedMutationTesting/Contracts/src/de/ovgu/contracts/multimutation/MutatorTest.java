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

import junit.framework.TestCase;

import org.junit.Test;

/**
 * 
 * @author Fabian Benduhn
 * 
 */
public class MutatorTest extends TestCase {

 
    public void testGetLineString() {
        String s = "a\nbcd";
        for (int i = 0; i < s.length(); i++) {
          //  System.out.println(Reader.getLineString(s, i));
        }
    }

    @Test
    public void test() {
        // TODO: replace with generic path
//        MultiMutator mutator = new MultiMutator(Defaults.CONTRACTS_PATH
//                + "features");
//        String mutationType = "MIXED";
//
//
//        ArrayList<MutationCase> cases = mutator.mutate(2,5);
//    
//
//        for (int i = 0; i < mutator.mutations.size(); i++) {
//            System.out.println("case " + i + ": " + cases.get(i));
            // System.out.println(cases.size());
            // System.out.println("Mutation  "
            // + i
            // + " "
            // + cases.get(i).relevantObjects.get(0).performedMutations
            // .get(cases.get(i)));
            // System.out.println("original");
            // System.out
            // .println(cases.get(i).relevantObjects.get(0).originalContent);
            // System.out.println("mutated:");
            // System.out
            // .println(cases.get(i).relevantObjects.get(0).mutatedContent
            // .get(cases.get(i)));
//        }
    }
}
