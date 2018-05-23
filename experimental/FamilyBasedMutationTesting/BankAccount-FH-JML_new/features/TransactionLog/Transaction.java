

/**
 * TODO description
 */
public class Transaction {
	/*@ public invariant transactions.length == 10; */
	public LogEntry[] transactions = new LogEntry[10];
	int transactionCounter = 0;
	
	/*@ 
	  @ requires \original;
	  @ ensures \original;
	  @ ensures \result ==> ( transactionCounter == (\old(transactionCounter) + 1 ) % 10);
	  @ ensures !\result ==> (transactionCounter == \old(transactionCounter));
	  @*/
	boolean transfer(Account source, Account destination, int amount) {
		if (original(source, destination, amount)) {
			transactionCounter = (transactionCounter + 1) % 10;
			transactions[transactionCounter] = new LogEntry(source, destination, amount);
			return true;
		}
		return false;
	}
}