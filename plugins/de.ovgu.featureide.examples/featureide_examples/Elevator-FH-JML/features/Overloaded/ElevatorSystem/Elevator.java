package ElevatorSystem;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Elevator {

	private boolean blocked = false;

	// specification 10
	/* Original: The Doors of the lift cannot be closed when the lift is overloaded.
	 * MyVersion: The doors are never closed when the lift is overloaded.
	 */
	 // specification 11
	 /* Elevator must not move while it is overloaded.
	  */
	/*@
	  @ ensures \original;
	  @ ensures weight > maximumWeight ==> areDoorsOpen();
	  @ ensures \old(weight) > \old(maximumWeight) ==> getCurrentFloorID() == \old(getCurrentFloorID());
	  @*/
	public void timeShift() {
		if (areDoorsOpen() && weight > maximumWeight) {
			blocked = true;
			if (verbose) System.out.println("Elevator blocked due to overloading (weight:" + weight + " > maximumWeight:" + maximumWeight + ")");
		} else {
			blocked = false;
			original();
		}
	}
	
	public boolean isBlocked() {
		return blocked;
	}
	
}
