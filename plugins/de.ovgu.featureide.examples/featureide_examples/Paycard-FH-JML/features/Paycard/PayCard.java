public class PayCard {
    
    /*@
      @ public instance invariant balance >= 0;
      @ public instance invariant limit > 0;
      @*/
    
    /*@ spec_public @*/ int limit=1000;
    /*@ spec_public @*/ int id;
    /*@ spec_public @*/ int balance=0;
    
    public PayCard(int limit) {
	balance = 0;
	this.limit=limit;
    }
    
    public PayCard() {
	balance=0;
    }
    
    /*@
      @ ensures \result.limit==100;
      @ assignable \nothing;
      @*/
    public static PayCard createJuniorCard() {
	return new PayCard(100);
    }
    
    /*@ \consecutive_contract
      @ public normal_behavior
      @ requires amount>0;
      @ {|
      @     requires amount + balance < limit && isValid() == true;
      @     ensures \result == true;
      @     ensures balance == amount + \old(balance);
      @     assignable balance;
      @
      @     also
      @
      @     requires amount + balance >= limit || isValid() == false;
      @     ensures \result == false;
      @		assignable \nothing;
      @ |}
      @ 	
      @ also
      @
      @ public exceptional_behavior
      @ requires amount <= 0;
      @*/
    public boolean charge(int amount) throws IllegalArgumentException {
	if (amount <= 0) {
	    throw new IllegalArgumentException();
	}
	if (this.balance+amount<this.limit && this.isValid()) {
	    this.balance=this.balance+amount;
	    return true;
	} else {
	    return false;
	}
    }
    
    /*@
      @ public normal_behavior
      @ requires amount>0;
      @ assignable \everything;
      @ ensures balance >= \old(balance);
      @*/
    public void chargeAndRecord(int amount) {
	    charge(amount);
    }
    
    /*@
      @ public normal_behavior
      @ requires true;
      @ ensures true; 
      @ assignable \nothing;
      @*/
    public /*@pure@*/ boolean isValid() {
	    return true;
    }
    
    public String infoCardMsg() {
	return (" Current balance on card is " + balance);
    }
}
