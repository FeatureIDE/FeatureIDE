public class Account {
	final int OVERDRAFT_LIMIT = 0;

	//@ invariant balance >= OVERDRAFT_LIMIT;
	int balance = 0;
	
	/*@
	 @ ensures balance == 0;
	 @*/
	Account() {
	}
	
	/*@
	 @ ensures (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) + x); 
	 @*/
	boolean update(int x) {
		int newBalance = balance + x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}

	/*@
	 @  ensures (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) - x);
	 @*/
	boolean undoUpdate(int x) {
		int newBalance = balance - x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}
	
}