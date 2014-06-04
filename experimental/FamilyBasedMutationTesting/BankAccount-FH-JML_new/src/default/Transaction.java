public  class Transaction {
	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.transaction;
	 @ requires FM.FeatureModel.transaction ==> (destination != null && source != null);
	 @ requires FM.FeatureModel.transaction ==> (source != destination);
	 @ ensures FM.FeatureModel.transaction ==> (\result ==> (\old(destination.balance) + amount == destination.balance));
	 @ ensures FM.FeatureModel.transaction ==> (\result ==> (\old(source.balance) - amount == source.balance));
	 @ ensures FM.FeatureModel.transaction ==> (!\result ==> (\old(destination.balance) == destination.balance));
	 @ ensures FM.FeatureModel.transaction ==> (!\result ==> (\old(source.balance) == source.balance));
	 @*/
	 private boolean  transfer__wrappee__Transaction  (Account source, Account destination, int amount) {
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
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.transactionlog || FM.FeatureModel.transaction;
	 @ requires !FM.FeatureModel.transactionlog ==> FM.FeatureModel.transaction ==> (source != destination);
	 @ requires !FM.FeatureModel.transactionlog ==> FM.FeatureModel.transaction ==> (destination != null && source != null);
	 @ requires FM.FeatureModel.transactionlog ==> (( FM.FeatureModel.transaction ==> (destination != null && source != null) ) && ( FM.FeatureModel.transaction ==> (source != destination) ));
	 @ ensures !FM.FeatureModel.transactionlog ==> FM.FeatureModel.transaction ==> (!\result ==> (\old(source.balance) == source.balance));
	 @ ensures !FM.FeatureModel.transactionlog ==> FM.FeatureModel.transaction ==> (!\result ==> (\old(destination.balance) == destination.balance));
	 @ ensures !FM.FeatureModel.transactionlog ==> FM.FeatureModel.transaction ==> (\result ==> (\old(source.balance) - amount == source.balance));
	 @ ensures !FM.FeatureModel.transactionlog ==> FM.FeatureModel.transaction ==> (\result ==> (\old(destination.balance) + amount == destination.balance));
	 @ ensures FM.FeatureModel.transactionlog ==> (( FM.FeatureModel.transaction ==> (\result ==> (\old(destination.balance) + amount == destination.balance)) ) && ( FM.FeatureModel.transaction ==> (\result ==> (\old(source.balance) - amount == source.balance)) ) && ( FM.FeatureModel.transaction ==> (!\result ==> (\old(destination.balance) == destination.balance)) ) && ( FM.FeatureModel.transaction ==> (!\result ==> (\old(source.balance) == source.balance)) ));
	 @ ensures FM.FeatureModel.transactionlog ==> (\result ==> ( transactionCounter == (\old(transactionCounter) + 1 ) % 10));
	 @ ensures FM.FeatureModel.transactionlog ==> (!\result ==> (transactionCounter == \old(transactionCounter)));
	 @*/
	boolean transfer(Account source, Account destination, int amount) {
		if (!FM.FeatureModel.transactionlog)
			return transfer__wrappee__Transaction(source, destination, amount);
		if (transfer__wrappee__Transaction(source, destination, amount)) {
			transactionCounter = (transactionCounter + 1) % 10;
			transactions[transactionCounter] = new LogEntry(source, destination, amount);
			return true;
		}
		return false;
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.transaction;
	 @ requires FM.FeatureModel.transaction ==> (destination != null && source != null);
	 @ requires FM.FeatureModel.transaction ==> (source != destination);
	 @ ensures FM.FeatureModel.transaction ==> (\result ==> source.isLocked() && destination.isLocked());
	 @*/
	private static synchronized boolean lock(Account source, Account destination) {
		if (source.isLocked()) return false;
		if (destination.isLocked()) return false;
		source.lock();
		destination.lock();
		return true;
	}

	/*@ public invariant FM.FeatureModel.transactionlog ==> (transactions.length == 10); @*/

	public LogEntry[] transactions = new LogEntry[10];

	int transactionCounter = 0;


}
