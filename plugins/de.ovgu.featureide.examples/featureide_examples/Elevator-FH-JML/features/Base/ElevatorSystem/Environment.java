package ElevatorSystem;

public class Environment {
	
	/* Specification 1:
	 * Pressing a landing Button guarantees that the lift will arrive at that landing and open the doors.
	 */
	/*@ model boolean[] calledAt_Spec1; @*/

	/*Specification 2:
	 * Pressing a button inside the lift guarantees that the lift will arrive at that landing and open the doors.
	 */
	/*@ model boolean[] calledAt_Spec2; @*/
		
	Floor[] floors;
	
	/*@
	  @ ensures (\forall int i; 0 <= i && i < calledAt_Spec1.length; !calledAt_Spec1[i]);
	  @ ensures (\forall int i; 0 <= i && i < calledAt_Spec1.length; !calledAt_Spec2[i]);
	  @*/
	public Environment(int numFloors) {
		/*@ set calledAt_Spec1 = new boolean[numFloors]; @*/
		/*@ set calledAt_Spec2 = new boolean[numFloors]; @*/
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
