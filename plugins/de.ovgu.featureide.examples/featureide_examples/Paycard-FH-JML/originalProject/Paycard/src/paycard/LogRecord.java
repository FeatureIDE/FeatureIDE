package paycard;

public class LogRecord {
    
    /*@ public instance invariant
      @     !empty ==> (balance >= 0 && transactionId >= 0);
      @ public static invariant transactionCounter >= 0;
      @*/
    
    private /*@ spec_public @*/ static int transactionCounter = 0;
    
    private /*@ spec_public @*/ int balance = -1;
    private /*@ spec_public @*/ int transactionId = -1;
    private /*@ spec_public @*/ boolean empty = true;
    
    public /*@pure@*/ LogRecord() {}
    
    
    /*@ public normal_behavior
      @   requires balance >= 0;
      @   assignable empty, this.balance, transactionId, transactionCounter;
      @   ensures this.balance == balance && 
      @           transactionId == \old(transactionCounter);
      @*/
    public void setRecord(int balance) throws CardException {
	if(balance < 0){
	    throw new CardException();
	}
	this.empty = false;
	this.balance = balance;
	this.transactionId = transactionCounter++;
    }
    
    /*@ public normal_behavior
      @   ensures \result == balance;
      @*/
    public /*@pure@*/ int getBalance() {
	return balance;
    }
    
    /*@ public normal_behavior
      @   ensures \result == transactionId;
      @*/
    public /*@pure@*/ int getTransactionId() {
	return transactionId;
    }
}
