package ElevatorSystem;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Elevator {

	Environment env;

	boolean verbose;

	int currentFloorID;
	public enum Direction {
		up { 
			@Override public Direction reverse() {return down;}	
		}, 
		down { 
			@Override public Direction reverse() {return up;}
		};
		public abstract Direction reverse();
	}

	Direction currentHeading;

	private List<Person> persons = new ArrayList<Person>();
	enum DoorState {open, close};

	DoorState doors;

	boolean[] floorButtons;
	
	public Elevator(Environment env, boolean verbose) {
		this.verbose = verbose;
		this.currentHeading = Direction.up;
		this.currentFloorID = 0;
		this.doors = DoorState.open;
		this.env = env;
		this.floorButtons = new boolean[env.floors.length];
	}
	public Elevator(Environment env, boolean verbose, int floor, boolean headingUp) {
		this.verbose = verbose;
		this.currentHeading = (headingUp ? Direction.up : Direction.down);
		this.currentFloorID = floor;
		this.doors = DoorState.open;
		this.env = env;
		this.floorButtons = new boolean[env.floors.length];
	}
	
	public boolean isBlocked() {
		return false;
	}
	
	public void enterElevator(Person p) {
		persons.add(p);
		p.enterElevator(this);
		if (verbose) System.out.println(p.getName() + " entered the Elevator at Landing " + this.getCurrentFloorID() + ", going to " + p.getDestination());
	}
	
	public boolean leaveElevator(Person p) {
		if (persons.contains(p)) {
			persons.remove(p);
			p.leaveElevator();
			if (verbose) System.out.println(p.getName() + " left the Elevator at Landing " + currentFloorID);
			return true;
		} else return false;
	}
	
	/**
	 * Activates the button for the given floor in the lift.
	 * @param floorID
	 */
	/*@ 
	  @ ensures env.calledAt_Spec2[floorID];
	  @*/
	public void pressInLiftFloorButton(int floorID) {
		/*@ set env.calledAt_Spec2[floorID] = true; @*/
		floorButtons[floorID] = true;
	}
	private void resetFloorButton(int floorID) {
		floorButtons[floorID] = false;
	}
	public /*@pure@*/  int getCurrentFloorID() {
		return currentFloorID;
	}
	
	public /*@pure@*/ boolean areDoorsOpen() {
		return doors == DoorState.open;
	}

	 /*Specification 3:
	  * The Lift will not change direction while there are calls in the direction it is traveling.
	  */
	// pre: elevator arrived at the current floor, next actions to be done
	/*@ 
	  @ ensures env.calledAt_Spec1[currentFloorID] == env.calledAt_Spec1[currentFloorID] && areDoorsOpen() ? false : env.calledAt_Spec1[currentFloorID];
	  @ ensures \old(getCurrentDirection()) == Direction.up && getCurrentDirection() == Direction.down ==> (\forall int i; getCurrentFloorID() < i && i < numFloors; !buttonForFloorIsPressed(i));
	  @ ensures \old(getCurrentDirection()) == Direction.down && getCurrentDirection() == Direction.up ==> (\forall int i; 0 <= i && i < getCurrentFloorID(); !buttonForFloorIsPressed(i));
	  @*/
	public void timeShift() {
		//System.out.println("--");
		
		if (stopRequestedAtCurrentFloor()) {
			//System.out.println("Arriving at " +  currentFloorID + ", Doors opening");
			doors = DoorState.open;
			// iterate over a copy of the original list, avoids concurrent modification exception
			for (Person p: new ArrayList<Person>(persons)) {
				if (p.getDestination() == currentFloorID) {
					leaveElevator(p);					
				}
			}
			env.getFloor(currentFloorID).processWaitingPersons(this);
			resetFloorButton(currentFloorID);
		} else {
			if (doors == DoorState.open)  {
				doors = DoorState.close;
				//System.out.println("Doors Closing");
			}
			if (stopRequestedInDirection(currentHeading, true, true)) {
				//System.out.println("Arriving at " + currentFloorID + ", continuing");
				// continue
				continueInDirection(currentHeading);
			} else if (stopRequestedInDirection(currentHeading.reverse(), true, true)) {
				//System.out.println("Arriving at " + currentFloorID + ", reversing direction because of call in other direction");
				// revert direction
				continueInDirection(currentHeading.reverse());
			} else {
				//idle
				//System.out.println("Arriving at " + currentFloorID + ", idle->continuing");
				continueInDirection(currentHeading);
			}
		}
		/*@ set env.calledAt_Spec1[currentFloorID] = env.calledAt_Spec1[currentFloorID] && areDoorsOpen() ? false : env.calledAt_Spec1[currentFloorID] @*/
	}

	private boolean stopRequestedAtCurrentFloor() {
		return env.getFloor(currentFloorID).hasCall() 
				|| floorButtons[currentFloorID] == true;
	}
	
	private void continueInDirection(Direction dir) {
		currentHeading = dir;
		if (currentHeading == Direction.up) {
			if (env.isTopFloor(currentFloorID)) {
				//System.out.println("Reversing at Top Floor");
				currentHeading = currentHeading.reverse();
			}
		} else { 
			if (currentFloorID == 0) {
				//System.out.println("Reversing at Basement Floor");
				currentHeading = currentHeading.reverse();
			}
		}
		if (currentHeading == Direction.up) {
			currentFloorID = currentFloorID + 1;
		} else {
			currentFloorID = currentFloorID - 1;
		}
	}

	
	private boolean isAnyLiftButtonPressed() {
		for (int i = 0; i < this.floorButtons.length; i++) {
			if (floorButtons[i]) return true;
		}
		return false;
	}
	
	private boolean stopRequestedInDirection (Direction dir, boolean respectFloorCalls, boolean respectInLiftCalls) {
		Floor[] floors = env.getFloors();
		if (dir == Direction.up) {
			if (env.isTopFloor(currentFloorID)) return false;
			for (int i = currentFloorID+1; i < floors.length; i++) {
				if (respectFloorCalls && floors[i].hasCall()) return true;
				if (respectInLiftCalls && this.floorButtons[i]) return true; 
			}
			return false;
		} else {
			if (currentFloorID == 0) return false;
			for (int i = currentFloorID-1; i >= 0; i--) {
				if (respectFloorCalls && floors[i].hasCall()) return true;
				if (respectInLiftCalls && this.floorButtons[i]) return true;
			}
			return false;
		}
	}
	private boolean anyStopRequested () {
		Floor[] floors = env.getFloors();
		for (int i = 0; i < floors.length; i++) {
			if (floors[i].hasCall()) return true;
			else if (this.floorButtons[i]) return true; 
		}
		return false;		
	}

	public /*@pure@*/  boolean buttonForFloorIsPressed(int floorID) {
		return this.floorButtons[floorID];
	}

	public /*@pure@*/  Direction getCurrentDirection() {
		return currentHeading;
	}
	public Environment getEnv() {
		return env;
	}
	public boolean isEmpty() {
		return this.persons.isEmpty();
	}
	public boolean isIdle() {
		return !anyStopRequested();
	}
	
	@Override
	public String toString() {
		return "Elevator " + (areDoorsOpen() ? "[_]" :  "[] ") + " at " + currentFloorID + " heading " + currentHeading;
	}
	
}
