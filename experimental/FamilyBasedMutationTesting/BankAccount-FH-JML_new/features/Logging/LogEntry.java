/**
 * TODO description
 */
public class LogEntry {

	//@ private invariant source != null;
	private Account source;
	//@ private invariant destination != null;
	private Account destination;
	private int value;
	
	/*@
	  @ requires source != null;
	  @ requires destination != null;
	  @ requires source != destination;
	  @*/
	public LogEntry(Account source,Account destination,int amount){
		this.source = source;
		this.destination = destination;
		this.value = amount;
	}
	
	/*@
	  @ ensures \result != null;
	  @*/
	public /*@ pure @*/ Account getSource(){
		return source;
	}
	
	/*@
	  @ ensures \result != null;
	  @*/
	public /*@ pure @*/ Account getDestination(){
		return destination;
	}
	
	public /*@ pure @*/ int getAmount(){
		return value;
	}
	
}