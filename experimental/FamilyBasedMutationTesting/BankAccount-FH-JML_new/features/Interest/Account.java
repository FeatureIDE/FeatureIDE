class Account {

	final static int INTEREST_RATE = 2;

	int interest = 0;

	/*@
	  @ ensures (balance >= 0 ==> \result >= 0) 
	  @   && (balance <= 0 ==> \result <= 0);
	  @*/
	/*@ pure @*/ int calculateInterest() {
		return balance * INTEREST_RATE / 36500;
	}

}