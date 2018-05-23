public class Transaction {

	/*@ requires destination != null && source != null;
	  requires source != destination;
	  ensures \result ==> (\old(destination.balance) + amount == destination.balance);
	  ensures \result ==> (\old(source.balance) - amount == source.balance);
	  ensures !\result ==> (\old(destination.balance) == destination.balance);
	  ensures !\result ==> (\old(source.balance) == source.balance); @*/
	public boolean transfer(Account source, Account destination, int amount) {
		if (!lock(source, destination)) return false;
		try {
			if (amount <= 0) {
				return false;
			}
			if (!source.update(amount * -1)) {
				return false;
			}
			if (!destination.update(amount)) {
				source.undoUpdate(amount * -1);
				return false;
			}
			return true;
		} finally {
			source.unLock();
			destination.unLock();
		}
	}

	/*@
	  requires destination != null && source != null;
	  requires source != destination;
	  ensures \result ==> source.isLocked() && destination.isLocked();
	 @*/
	private static synchronized boolean lock(Account source, Account destination) {
		if (source.isLocked()) return false;
		if (destination.isLocked()) return false;
		source.lock();
		destination.lock();
		return true;
	}
}
