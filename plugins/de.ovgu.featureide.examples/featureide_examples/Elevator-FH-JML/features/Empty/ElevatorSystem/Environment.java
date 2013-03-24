package ElevatorSystem;

public class Environment {
	
	 // specification 9
	 /*
	  * The Lift will honor Requests from within the lift as long as it is not empty.
	  * (this is actually a copy of Spec2 with added property that the lift is not empty.
	  */
	/*@ model boolean[] calledAt_Spec9; @*/
	
	public Environment(int numFloors) {
		floors = new Floor[numFloors];
		for (int i = 0; i < numFloors; i++) {
			floors[i] = new Floor(this, i);
		}
	}
	
	public Floor getFloor(int id) {
		return floors[id];
	}
	public Floor[] getFloors() {
		return floors;
	}
	public boolean isTopFloor(int id) {
		return id == floors.length-1;
	}
}
