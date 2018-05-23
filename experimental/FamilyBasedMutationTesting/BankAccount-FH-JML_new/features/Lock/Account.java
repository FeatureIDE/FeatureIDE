
public class Account {
	
	public boolean lock = false;
	
	/*@
	 @ ensures this.lock;
	 @*/
	void lock() {
		lock = true;
	}
	
	/*@
	 @ ensures !this.lock;
	 @*/
	void unLock() {
		lock = false;
	}
	
	/*@
	 @ ensures \result == this. lock;
	 @*/
	boolean isLocked() {
		return lock;
	}
}