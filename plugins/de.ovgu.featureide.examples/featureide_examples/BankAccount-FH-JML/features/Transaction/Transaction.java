public class Transaction {

	/*@ 
	  requires destination != null && source != null && source != destination;
	  requires amount > 0;
	  ensures \result ==> (\old(destination.getBalance()) + amount == destination.getBalance());
	  ensures \result ==> (\old(source.getBalance()) - amount == source.getBalance());
	  ensures !\result ==> (\old(destination.getBalance()) == destination.getBalance());
	  ensures !\result ==> (\old(source.getBalance()) == source.getBalance()); @*/
	public boolean transfer(Account source, Account destination, int amount) {
		if (!lock(source, destination)) return false;
		try {
			if (amount <= 0) {
				return false;
			} 
			if (!source.withdraw(amount)) {
				return false;
			}
			if (!destination.deposit(amount)) {
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
