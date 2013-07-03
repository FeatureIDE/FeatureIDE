class Account {

	final static int INTEREST_RATE = 2;

	int interest = 0;
	/*@
	 @ ensures \result == interest;
	 @*/
	/*@ pure @*/ int getInterest() {
		return interest;
	}
	
	/*@
	  @ ensures (balance >= 0 ==> \result >= 0) 
	  @   && (balance <= 0 ==> \result <= 0);
	  @*/
	/*@ pure @*/ int calculateInterest() {
		return balance * INTEREST_RATE / 36500;
	}
	
	/*@
	 @ requires canUpdate(interest);
	 @ ensures balance == \old(balance) + \old(interest) && interest == 0;
	 @*/
	void applyInterrest() {
		update(interest);
		interest = 0;
	}
	
	/*@
	 @ 
	 @*/
	void increaseInterrest() {
		interest += calculateInterest();
	}

}