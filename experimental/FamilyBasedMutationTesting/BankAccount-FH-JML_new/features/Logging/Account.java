

/**
 * TODO description
 */
public class Account {

	public int[] updates = new int[10];
	public int updateCounter = 0;
	public int[] undoUpdates = new int[10];
	public int undoUpdateCounter = 0;
			
	/*@ 
	  @ ensures \original;
	  @ ensures \result ==> this.updates[this.updateCounter] == x;
	  @ ensures \result ==> this.updateCounter == ( \old(this.updateCounter) + 1 ) % 10;
	  @ ensures !\result ==> this.updateCounter == \old(this.updateCounter);
	  @*/
	boolean update(int x){
		if (original(x)){
			updateCounter = (updateCounter + 1) % 10;
			updates[updateCounter] = x;
			return true;
		}
		return false;
		
	}
	
	/*@ 
	  @ ensures \original;
	  @ ensures \result ==> this.undoUpdates[this.undoUpdateCounter] == x;
	  @ ensures \result ==> this.undoUpdateCounter == ( \old(this.undoUpdateCounter) + 1 ) % 10;
	  @ ensures !\result ==> this.undoUpdateCounter == \old(this.undoUpdateCounter);
	  @*/
	boolean undoUpdate(int x){
		if (original(x)){
			undoUpdateCounter = (undoUpdateCounter + 1) % 10;
			undoUpdates[undoUpdateCounter] = x;
			return true;
		}
		return false;
		
	}
	
}