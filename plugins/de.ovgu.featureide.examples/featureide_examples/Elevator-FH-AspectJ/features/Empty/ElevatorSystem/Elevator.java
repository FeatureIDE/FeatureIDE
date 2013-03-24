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
}
