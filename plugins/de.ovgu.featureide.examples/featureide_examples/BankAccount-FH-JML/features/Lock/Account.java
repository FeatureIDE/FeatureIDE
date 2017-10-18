
public class Account {
	
	private boolean lock = false;
	
	/*@
	 @ ensures this.lock;
	 @ assignable lock;
	 @*/
	void lock() {
		lock = true;
	}
	
	/*@
	 @ ensures !this.lock;
	 @ assignable lock;
	 @*/
	void unLock() {
		lock = false;
	}
	
	/*@
	 @ ensures \result == this. lock;
	 @ assignable \nothing;
	 @*/
	boolean isLocked() {
		return lock;
	}
}