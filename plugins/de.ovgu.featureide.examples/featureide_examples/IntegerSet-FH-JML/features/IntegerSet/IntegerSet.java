//@ model import org.jmlspecs.models.*;

/** Sets of integers. */
public class IntegerSet {
    //@ public model instance JMLValueSet theSet;
	//@ public instance invariant_redundantly theSet != null;
	//@ public initially theSet.isEmpty();
	//@ public instance invariant
	//@       (\forall JMLType e; theSet.has(e);
	//@                           e instanceof JMLInteger);
     
	public int dummy;

    /** Insert the given integer into this set. */
    /*@ public normal_behavior
      @	  assignable theSet;
      @	  ensures theSet.equals(\old(theSet.insert(new JMLInteger(elem))));
      @*/
    public void insert(int elem){
    	
    }

    /** Tell if the argument is in this set. */
    /*@ public normal_behavior	
      @	  ensures \result == theSet.has(new JMLInteger(elem));
      @*/
    public /*@ pure @*/ boolean isMember(int elem){
    	
    } 

    /** Remove the given integer from this set. */
    /*@ public normal_behavior
      @   assignable theSet;
      @   ensures theSet.equals( \old(theSet.remove(new JMLInteger(elem))) );
      @*/
    public void remove(int elem){
    	
    }
}
