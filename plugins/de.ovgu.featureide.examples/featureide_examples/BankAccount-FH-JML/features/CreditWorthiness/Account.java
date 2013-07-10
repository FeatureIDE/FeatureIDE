class Account {

	/*@
	 @ requires amount >= 0;
	 @ ensures balance.getValue() >= amount <==> \result;
	 @*/
	boolean credit(int amount) {
		return balance >= amount;
	}

}