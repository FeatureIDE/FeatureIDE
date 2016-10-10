package paycard;

public class PayCard {
    
    /*@
      @ public instance invariant balance >= 0;
      @ public instance invariant limit > 0;
      @ public instance invariant unsuccessfulOperations >= 0;
      @*/
    
    /*@ spec_public @*/ int limit=1000;
    /*@ spec_public @*/ int unsuccessfulOperations;
    /*@ spec_public @*/ int id;
    /*@ spec_public @*/ int balance=0;
    /*@ spec_public @*/ protected LogFile log;
    
    public PayCard(int limit) {
	balance = 0;
	unsuccessfulOperations=0;
	this.limit=limit;
    }
    
    public PayCard() {
	balance=0;
	unsuccessfulOperations=0;
    }
    
    /*@
      @ ensures \result.limit==100;
      @*/
    public static PayCard createJuniorCard() {
	return new PayCard(100);
    }
    
    /*@
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
      @     ensures unsuccessfulOperations == \old(unsuccessfulOperations) + 1; 
      @     assignable unsuccessfulOperations;
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
	    this.unsuccessfulOperations++;
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
	if (charge(amount)) {
	    try {
		log.addRecord(balance);
	    } catch (CardException e){
		throw new IllegalArgumentException();
	    }
	}
    }
    
    /*@
      @ public normal_behavior
      @ requires true;
      @ ensures \result == (unsuccessfulOperations<=3); 
      @ assignable \nothing;
      @*/
    public /*@pure@*/ boolean isValid() {
	if (unsuccessfulOperations<=3) {
	    return true;
	} else {
	    return false;
	}
    }
    
    public String infoCardMsg() {
	return (" Current balance on card is " + balance);
    }
}
