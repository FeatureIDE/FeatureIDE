class Account {

	/*@
	 @ requires amount >= 0;
	 @ ensures balance >= amount <==> \result;
	 @ assignable \nothing;
	 @*/
	boolean credit(int amount) {
		return balance >= amount;
	}

}