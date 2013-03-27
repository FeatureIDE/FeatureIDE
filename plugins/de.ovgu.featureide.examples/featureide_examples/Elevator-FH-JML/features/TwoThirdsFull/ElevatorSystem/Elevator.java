package ElevatorSystem;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Elevator {

	private boolean stopRequestedAtCurrentFloor() {
		if (weight > maximumWeight*2/3) {
			return floorButtons[currentFloorID] == true;
		} else return original();
	}
	
	private boolean stopRequestedInDirection (Direction dir, boolean respectFloorCalls, boolean respectInLiftCalls) {
		if (weight > maximumWeight*2/3 && isAnyLiftButtonPressed()) {
			if (verbose) System.out.println("over 2/3 threshold, ignoring calls from FloorButtons until weight is below 2/3*threshold");
			return original(dir, false, respectInLiftCalls);
		} else return original(dir, respectFloorCalls, respectInLiftCalls);
	}
	
	// specification 13
	// Car calls have precedence when the Lift is two thirds full.
	/*@
	  @ ensures \original;
	  @ ensures getCurrentFloorID() != \old(getCurrentFloorID()) &&
	  @   weight > maximumWeight*2/3 ==> 
	  @ 	(\old(getCurrentDirection()) == Direction.up &&
	  @ 	 existInLiftCallsInDirection(Direction.down) && 
	  @ 	 !existInLiftCallsInDirection(Direction.up) ==>
	  @ 	 getCurrentDirection() != Direction.up) &&
	  @ 	(\old(getCurrentDirection()) == Direction.down &&
	  @ 	 existInLiftCallsInDirection(Direction.up) && 
	  @ 	 !existInLiftCallsInDirection(Direction.down) ==>
	  @ 	 getCurrentDirection() != Direction.down);
	  @*/
	private void continueInDirection(Direction dir) {
		original(dir);
	}

	private /*@pure@*/  boolean existInLiftCallsInDirection(Direction d) {
		 if (d == Direction.up) {
			 for (int i = getCurrentFloorID(); i < floorButtons.length; i++)
				 if (buttonForFloorIsPressed(i)) return true;
		 } else if (d == Direction.down) {
			 for (int i = getCurrentFloorID(); i >= 0; i--)
				 if (buttonForFloorIsPressed(i)) return true;
		 }
		 return false;		 
	 }

}
