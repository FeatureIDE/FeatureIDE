class Account {
	/*@ invariant withdraw >= DAILY_LIMIT; @*/
	
	final static int DAILY_LIMIT = -1000;
	
	int withdraw = 0;

	/*@ \consecutive_contract
	 @
	 @ ensures (!\result ==> withdraw == \old(withdraw)) 
	 @   && (\result ==> withdraw <= \old(withdraw));
	 @ assignable withdraw;
	 @*/
	boolean update(int x) {
		int newWithdraw = withdraw;
		if (x < 0)  {
			newWithdraw += x;
			if (newWithdraw < DAILY_LIMIT) 
				return false;
		}
		if (!original(x))
			return false;
		withdraw = newWithdraw;
		return true;
	}
	
	/*@ \consecutive_contract
	 @
	 @ ensures (!\result ==> withdraw == \old(withdraw)) 
	 @   && (\result ==> withdraw >= \old(withdraw));
	 @ assignable withdraw;
	 @*/
	boolean undoUpdate(int x) {
		int newWithdraw = withdraw;
		if (x < 0)  {
			newWithdraw -= x;
			if (newWithdraw < DAILY_LIMIT) 
				return false;
		}
		if (!original(x))
			return false;
		withdraw = newWithdraw;
		return true;
	}
		
}