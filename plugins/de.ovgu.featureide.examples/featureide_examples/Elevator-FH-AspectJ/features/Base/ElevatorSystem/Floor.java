package ElevatorSystem;
//import gov.nasa.jpf.symbc.Symbolic;

import java.util.ArrayList;
import java.util.List;


public class Floor {
	//@Symbolic("false")
	private final int thisFloorID;
	//@Symbolic("false")
	private boolean elevatorCall = false;
	//@Symbolic("false")
	private List<Person> waiting = new ArrayList<Person>();
	
	public Floor(int id) {
		thisFloorID = id;
	}
	public int getFloorID() {
		return this.thisFloorID;
	}
	
	public void callElevator() {
		elevatorCall = true;
	}
	public void reset() {
		elevatorCall = false;
	}
	
	public boolean hasCall() {
		return elevatorCall;
	}
	public void processWaitingPersons(Elevator e) {
		for (Person p : waiting) {
			e.enterElevator(p);
		}
		waiting.clear();
		reset();
	}
	public void addWaitingPerson(Person person) {
		waiting.add(person);
		callElevator();
	}
}
