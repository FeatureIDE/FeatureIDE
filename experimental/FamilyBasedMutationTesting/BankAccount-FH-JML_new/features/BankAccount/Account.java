public class Account {
	public final int OVERDRAFT_LIMIT = 0;

	/*@ public invariant this.balance >= OVERDRAFT_LIMIT; */
	public int balance = 0;
	
	/*@
	 @ ensures balance == 0;
	 @*/
	Account() {
	}
	
	/*@
	 @ requires x != 0;
	 @ ensures (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) + x); 
	 @*/
	boolean update(int x) {
		int newBalance = balance + x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = balance + x;
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