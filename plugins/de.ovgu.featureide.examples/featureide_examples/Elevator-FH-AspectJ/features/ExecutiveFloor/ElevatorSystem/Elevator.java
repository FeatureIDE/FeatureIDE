package ElevatorSystem;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;


public class Elevator {
	int executiveFloor = 4;
	public boolean isExecutiveFloor(int floorID) {return floorID == executiveFloor; }
	//private boolean isExecutiveFloor(Floor floor) {return floor.getFloorID() == executiveFloor; }
	public boolean isExecutiveFloorCalling() {
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
}
