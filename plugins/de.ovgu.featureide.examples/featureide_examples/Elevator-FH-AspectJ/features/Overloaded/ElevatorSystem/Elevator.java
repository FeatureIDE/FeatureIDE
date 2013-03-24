package ElevatorSystem;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;


public class Elevator {
	private boolean blocked = false;
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
