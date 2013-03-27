package ElevatorSystem;

import java.util.ArrayList;
import java.util.List;

public class Floor {

	private final int thisFloorID;

	private boolean elevatorCall = false;

	private List<Person> waiting = new ArrayList<Person>();
	
	private Environment env;
	
	public Floor(Environment env, int id) {
		this.env = env;
		thisFloorID = id;
	}
	
	public int getFloorID() {
		return this.thisFloorID;
	}
	
	/*@
	  @ ensures env.calledAt_Spec1[floor.getFloorID()];
	  @*/
	public void callElevator() {
		/*@ set env.calledAt_Spec1[floor.getFloorID()] = true; @*/
		elevatorCall = true;
	}
	
	public void reset() {
		elevatorCall = false;
	}
	
	public /*@pure@*/  boolean hasCall() {
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
