class Account {

	final static int DAILY_LIMIT = -1000;
	
	//@ invariant withdraw >= DAILY_LIMIT;
	int withdraw = 0;

	/*@
	 @ ensures \original 
	 @   && (!\result ==> withdraw == \old(withdraw)) 
	 @   && (\result ==> withdraw <= \old(withdraw));
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
	
	/*@
	 @ ensures \original 
	 @   && (!\result ==> withdraw == \old(withdraw)) 
	 @   && (\result ==> withdraw >= \old(withdraw));
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