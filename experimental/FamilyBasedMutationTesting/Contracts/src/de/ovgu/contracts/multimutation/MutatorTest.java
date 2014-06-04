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
