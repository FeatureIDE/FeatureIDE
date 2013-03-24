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
}
