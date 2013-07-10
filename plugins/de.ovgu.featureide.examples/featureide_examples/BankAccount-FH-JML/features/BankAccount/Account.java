public class Account {
	
	private final /*@ spec_public @*/ Money OVERDRAFT_LIMIT = new Money(0);
	//@ public invariant balance != null;
	//@ public invariant balance.getValue() >= OVERDRAFT_LIMIT.getValue();
	private /*@ spec_public @*/ Money balance;
	
	/*@
	 @ ensures \result == balance;
	 @*/
	public /*@ pure @*/ Money getBalance() {
		return balance;
	}
	
	/*@
	 @ ensures balance.getValue() == 0;
	 @*/
	public Account() {
		this(0);
	}
	
	/*@
	 @ requires value >= 0;
	 @ ensures balance.getValue() == value;
	 @*/
	public Account(int value) {
		balance = new Money(value);
	}
	
	/*@ 
	 @ requires value > 0; 
	 @ ensures (!\result ==> (balance.getValue() == \old(balance.getValue()))) 
	 @   && (\result ==> (balance.getValue() == \old(balance.getValue()) - value)); 
	 @*/
	public boolean withdraw(int value) {
		if (canUpdate(-1 * value)) {
			update(-1 * value);
			return true;
		}
		return false;
	}
	
	/*@
	 @ requires value > 0; 
	 @ ensures (!\result ==> balance.getValue() == \old(balance.getValue())) 
	 @   && (\result ==> balance.getValue() == \old(balance.getValue()) + value);  
	 @*/
	public boolean deposit(int value) {
		if (canUpdate(value)) {
			update(value);
			return true;
		}
		return false;
	}
	
	/*@ 
	 @ requires canUpdate(value); 
	 @ ensures (balance.getValue() == \old(balance.getValue()) + value); 
	 @*/
	private void update(int value) {
		balance.updateValue(value);
	}
	
	private /*@ pure @*/ boolean canUpdate(int value) {
		return balance.getValue() + value >= OVERDRAFT_LIMIT.getValue();
	}

	/**
	 * it is neccessary to undo an update and to set all fields to their original values 
	 * when it undo is called, even if update(x) would not be possible
	 * 
	 * invariants must be defined @ requires clauses
	 */
	/*@
	 @ requires balance.getValue() - value >= OVERDRAFT_LIMIT.getValue();
	 @ ensures balance.getValue() == \old(balance.getValue()) - value;
	 @*/
	void undoUpdate(int value) { 
		balance.updateValue(-value);
	}
	
	/*@
	 @ requires canUpdate(value);
	 @ ensures balance.getValue() == \old(balance.getValue());
	 @*/
	private void undoUpdateTest(int value) {
		update(value);
		undoUpdate(value);
	}
}