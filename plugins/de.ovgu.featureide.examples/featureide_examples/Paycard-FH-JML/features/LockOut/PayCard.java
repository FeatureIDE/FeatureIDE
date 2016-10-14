public class PayCard {
    
    /*@
      @ public instance invariant unsuccessfulOperations >= 0;
      @*/
    
    /*@ spec_public @*/ int unsuccessfulOperations = 0;
    
    /*@ public normal_behavior
      @ requires amount>0;
      @ requires amount + balance >= limit || isValid() == false;
      @ ensures unsuccessfulOperations == \old(unsuccessfulOperations) + 1; 
      @ assignable unsuccessfulOperations;
      @*/
    public boolean charge(int amount) throws IllegalArgumentException {
    	boolean success = original(amount);
    	if (!success)
    		this.unsuccessfulOperations++;
	    return success;
    }
    
    // contract remains identical
    public /*@pure@*/ boolean isValid() {
	if (unsuccessfulOperations<=3) {
	    return true;
	} else {
	    return false;
	}
    }

}
