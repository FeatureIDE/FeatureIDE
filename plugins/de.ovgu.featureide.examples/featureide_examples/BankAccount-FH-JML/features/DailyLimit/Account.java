class Account {

	private final static int DAILY_LIMIT = -1000;
	
	//@ invariant withdraw >= DAILY_LIMIT;
	private int withdraw = 0;
	
	/*@
	 @ ensures withdraw == 0;
	 @*/
	public void resetWithdraw() {
		withdraw = 0;
	}
	
	/*@
	 @ ensures \result == withdraw;
	 @*/
	public int getWithdraw() {
		return withdraw;
	}

	/*@
	 @ requires \original;
	 @ ensures \original && x < 0 ==> withdraw == \old(withdraw) + x && withdraw <= \old(withdraw);
	 @*/
	private void update(int x) {
		original(x);
		if (x < 0) {
			withdraw += x;
		}
	}
	
	/*@
	 @ assignable canUpdate;
	 @ ensures \original;
	 @*/
	private /*@ pure @*/ boolean canUpdate(int x) {
		boolean res = original(x) && withdraw + x >= DAILY_LIMIT;
		//@ set canUpdate = canUpdate && withdraw + x >= DAILY_LIMIT;
		return res;
	}
	
	/*@
	 @ requires \original && withdraw - x < DAILY_LIMIT; 
	 @ ensures \original;
	 @*/
	void undoUpdate(int x) {
		if (x < 0)  {
			withdraw -= x;
		}
		original(x);
	}
	
	/*@
	 @ requires \original;
	 @ ensures \original && withdraw == \old(withdraw);
	 @*/
	private void undoUpdateTest(int x) {
		original(x);
	}
}