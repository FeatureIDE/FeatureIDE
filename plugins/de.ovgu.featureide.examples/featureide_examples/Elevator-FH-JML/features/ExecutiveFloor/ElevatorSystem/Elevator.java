package ElevatorSystem;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Elevator {

	int executiveFloor = 4;
	
	public /*@pure@*/  boolean isExecutiveFloor(int floorID) {return floorID == executiveFloor; }

	//private boolean isExecutiveFloor(Floor floor) {return floor.getFloorID() == executiveFloor; }

	public /*@pure@*/  boolean isExecutiveFloorCalling() {
		for (Floor f : env.floors) 
			if (f.getFloorID() == executiveFloor && f.hasCall()) return true;
		return false;
	}
	
	// alternative implementation: subclass of "ExecutiveFloor extends Floor"
	private boolean stopRequestedAtCurrentFloor() { //executive
		if (isExecutiveFloorCalling() && !isExecutiveFloor(currentFloorID)) {
			return false;
		} else return original();
	}
	
	private boolean stopRequestedInDirection (Direction dir, boolean respectFloorCalls, boolean respectInLiftCalls) {
		if (isExecutiveFloorCalling()) {
			if (verbose) System.out.println("Giving Priority to Executive Floor");
			return ((this.currentFloorID < executiveFloor)  == (dir == Direction.up));
			
		} else return original(dir, respectFloorCalls, respectInLiftCalls);
	}
	
	// specification 14
	/* Original: The Lift will answer requests from the executive Floor.
	 * My Version: While there is a request from the executive Floor the lift will not open its doors somewhere else.
	 */
	/*@ 
	  @ ensures isExecutiveFloorCalling() && areDoorsOpen() ==> isExecutiveFloor(e.getCurrentFloorID());
	  @*/
	public void timeShift() {
		original();
	}

}
