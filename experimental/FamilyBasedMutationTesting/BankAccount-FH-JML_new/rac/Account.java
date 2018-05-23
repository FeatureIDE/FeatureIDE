

/**
 * TODO description
 */
public class Account {

	int[] updates = new int[10];
	int updateCounter = 0;
	int[] undoUpdates = new int[10];
	int undoUpdateCounter = 0;
			
	/*@ 
	  @ ensures \original;
	  @ ensures \result ==> updates[updateCounter] == x;
	  @*/
	boolean update(int x){
		if (original(x)){
			if (updateCounter == 9){
				for (int i = 0; i < 9 ; i++)
					updates[i] = updates[i+1];
			} else {
				updateCounter++;
			}
			updates[updateCounter] = x;
			return true;
		}
		return false;
		
	}
	
	/*@ 
	  @ ensures \original;
	  @ ensures \result ==> undoUpdates[undoUpdateCounter] == x;
	  @*/
	boolean undoUpdate(int x){
		if (original(x)){
			if (undoUpdateCounter == 9){
				for (int i = 0; i < 9 ; i++)
					undoUpdates[i] = undoUpdates[i+1];
			} else {
				undoUpdateCounter++;
			}
			undoUpdates[undoUpdateCounter] = x;
			return true;
		}
		return false;
		
	}
	
}