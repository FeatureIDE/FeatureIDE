package ElevatorSystem;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;


public class Elevator {
	//TODO: implement the weight property in Persons in this Feature
	int weight;
	private static final int maximumWeight = 100;
	
	public boolean leaveElevator(Person p) {
		if (original(p)) {
			weight-=p.getWeight();
			return true;
		} else return false;
	}
	public void enterElevator(Person p) {
		original(p);
		weight+=p.getWeight();
	}
}
