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
