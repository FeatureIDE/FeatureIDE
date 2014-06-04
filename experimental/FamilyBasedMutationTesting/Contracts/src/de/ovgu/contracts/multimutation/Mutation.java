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
