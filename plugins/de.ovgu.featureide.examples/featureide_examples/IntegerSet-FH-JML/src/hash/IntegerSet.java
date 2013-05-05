//@ model import org.jmlspecs.models.*;
import java.util.*; 



public   class  IntegerSet {
	
    //@ public model instance JMLValueSet theSet;
	//@ public instance invariant_redundantly theSet != null;
	//@ public initially theSet.isEmpty();
	//@ public instance invariant
	//@       (\forall JMLType e; theSet.has(e);
	//@                           e instanceof JMLInteger);
     
	public int dummy;

	/*@ 

    
     public normal_behavior
       assignable theSet;
       ensures theSet.equals(\old(theSet.insert(new JMLInteger(elem)))); @*/
	
    
    


    public void insert  (int i) {
        hset.add(new Integer(i));
    }

	/*@ 

    
     public normal_behavior	
       ensures \result == theSet.has(new JMLInteger(elem)); @*/
	
    //@                      in theSet;
    //@                      maps hset.theSet \into theSet;
    //@ private represents theSet <- abstractValue();
    
    public /*@pure@*/ boolean isMember  (int i) {
        return hset.contains(new Integer(i));
    }

	/*@  

    
     public normal_behavior
       assignable theSet;
       ensures theSet.equals( \old(theSet.remove(new JMLInteger(elem))) ); @*/
	



   

    public void remove  (int i) {
        hset.remove(new Integer(i));
    }

	
	   //@
	  //@  private pure model JMLValueSet abstractValue() {
	  //@      JMLValueSet ret = new JMLValueSet();
	  //@     Iterator iter = hset.iterator();
	  //@    while (iter.hasNext()) {
	  //@        ret = ret.insert(new JMLInteger((Integer)iter.next()));
	  //@    }
	  //@     return ret;
	  //@  } 
	    
    private  /*@non_null@*/  HashSet hset;

	/*@ 
    
    
     public normal_behavior
       assignable theSet;
       ensures theSet != null && theSet.isEmpty(); @*/
	
      
    public IntegerSet() {
        hset = new HashSet();
    }


	

    public String toString() {
        return hset.toString();
    }


}
