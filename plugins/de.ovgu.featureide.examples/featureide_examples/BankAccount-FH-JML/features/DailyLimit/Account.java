class Account {

	private final /*@ spec_public @*/ Money DAILY_LIMIT = new Money(-1000);
	
	//@ public invariant withdraw.getValue() >= DAILY_LIMIT.getValue();
	//@ public invariant withdraw != null;
	private /*@ spec_public @*/ Money withdraw = new Money(0);
	
	/*@
	 @ ensures withdraw.getValue() == 0;
	 @*/
	public void resetWithdraw() {
		withdraw.setValue(0);
	}
	
	/*@
	 @ ensures \result == withdraw;
	 @*/
	public Money getWithdraw() {
		return withdraw;
	}

	/*@
	 @ requires \original;
	 @ ensures \original && value < 0 ==> withdraw.getValue() == \old(withdraw.getValue()) + value && withdraw.getValue() <= \old(withdraw.getValue());
	 @*/
	private void update(int value) {
		original(value);
		if (value < 0) {
			withdraw.updateValue(value);
		}
	}

	private /*@ pure @*/ boolean canUpdate(int value) {
		return original(value) && withdraw.getValue() + value >= DAILY_LIMIT.getValue();
	}
	
	/*@
	 @ requires \original && withdraw.getValue() - value < DAILY_LIMIT.getValue(); 
	 @ ensures \original;
	 @*/
	void undoUpdate(int value) {
		if (value < 0)  {
			withdraw.updateValue(-value);
		}
		original(value);
	}
	
	/*@
	 @ requires \original;
	 @ ensures \original && withdraw.getValue() == \old(withdraw.getValue());
	 @*/
	private void undoUpdateTest(int value) {
		original(value);
	}
}