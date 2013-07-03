public class Account {
	
	private final int OVERDRAFT_LIMIT = 0;
	//@ private ghost boolean canUpdate;
	//@ invariant balance >= OVERDRAFT_LIMIT;
	private int balance;
	
	/*@
	 @ ensures \result == balance;
	 @*/
	/*@ pure @*/ int getBalance() {
		return balance;
	}
	
	/*@
	 @ ensures balance == 0;
	 @*/
	public Account() {
		balance = 0;
	}
	
	/*@
	 @ requires initialValue >= 0;
	 @ ensures balance == initialValue;
	 @*/
	public Account(int initialValue) {
		balance = initialValue;
	}
	
	/*@ 
	 @ requires money > 0; 
	 @ ensures (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) - money); 
	 @*/
	public boolean withdraw(int money) {
		if (canUpdate(-1 * money)) {
			update(-1 * money);
			return true;
		}
		return false;
	}
	
	/*@
	 @ requires money > 0; 
	 @ ensures (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) + money);  
	 @*/
	public boolean deposit(int money) {
		if (canUpdate(money)) {
			update(money);
			return true;
		}
		return false;
	}
	
	/*@ 
	 @ requires canUpdate(x); 
	 @ ensures (balance == \old(balance) + x); 
	 @*/
	private void update(int x) {
		balance = balance + x;
	}
	
	/**
	 * all proves are closed for using contracts if this method has no contract.
	 */
	/*@
	 @ assignable canUpdate; 
	 @ ensures \result <==> canUpdate;
	 @*/
	private /*@ pure @*/ boolean canUpdate(int x) {
		//@ set canUpdate = balance + x >= OVERDRAFT_LIMIT; 
		return balance + x >= OVERDRAFT_LIMIT;
	}

	/**
	 * it is neccessary to undo an update and to set all fields to their original values 
	 * when it undo is called, even if update(x) would not be possible
	 * 
	 * invariants must be defined @ requires clauses
	 */
	/*@
	 @ requires balance - x >= OVERDRAFT_LIMIT;
	 @ ensures balance == \old(balance) - x;
	 @*/
	void undoUpdate(int x) { 
		balance = balance - x;
	}
	
	/*@
	 @ requires canUpdate(x);
	 @ ensures balance == \old(balance);
	 @*/
	private void undoUpdateTest(int x) {
		update(x);
		undoUpdate(x);
	}
}