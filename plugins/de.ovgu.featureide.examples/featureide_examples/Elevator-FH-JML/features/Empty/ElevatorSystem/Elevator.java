package ElevatorSystem;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;


public class Elevator {
	public boolean leaveElevator(Person p) { // empty
		if (original(p)) {
			if (this.persons.isEmpty())
				Arrays.fill(this.floorButtons, false);
			return true;
		} else return false;
	}
	
	// specification 8
	/* Original: The Lift will not arrive empty at a floor unless the button on that landing was pressed.
	 * MyVersion: The Lift will not arrive empty at a floor and open its doors unless the button on that landing was pressed.
	 */
	/*@ 
	  @ ensures \original;
	  @ ensures \old(isEmpty()) && areDoorsOpen() ==> floors[getCurrentFloorID()].hasCall();
	  @ ensures isEmpty() ==> (\forall int i; 0 <= i && i < env.calledAt_Spec9.length; !env.calledAt_Spec9[i]);
	  @*/
	public void timeShift() {
		original();
		//TODO how to set all calledAt_Spec9[i] = false for all i?
	}

	/*@ 
	  @ ensures \original; 
	  @ ensures env.calledAt_Spec9[floorID];
	  @*/
	public void pressInLiftFloorButton(int floorID) {
		/*@ set env.calledAt_Spec9[floorID] = true; @*/
		original(floorID);
	}
}
