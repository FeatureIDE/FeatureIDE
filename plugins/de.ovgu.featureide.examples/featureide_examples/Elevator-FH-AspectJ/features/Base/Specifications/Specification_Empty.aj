package Specifications;

import java.util.Arrays;

import ElevatorSystem.Elevator;
import ElevatorSystem.Floor;
import TestSpecifications.SpecificationException;
import TestSpecifications.SpecificationManager;


public privileged aspect Specification_Empty extends AbstractSpecification {
	// specification 8
	/* Original: The Lift will not arrive empty at a floor unless the button on that landing was pressed.
	 * MyVersion: The Lift will not arrive empty at a floor and open its doors unless the button on that landing was pressed.
	 */
	 pointcut timeShift(Elevator e) : execution(public void ElevatorSystem.Elevator.timeShift()) && target(e);
	 
	 boolean floorButtonPressed[];
	 boolean wasEmptyBeforeTimeStep = false;
	 
	 @Override
	public void reset() {
		super.reset();
		if (SpecificationManager.checkSpecification(8)) {
			floorButtonPressed=null;
			wasEmptyBeforeTimeStep = false;
		}
	}
	 
	 before(Elevator e) : timeShift(e) {
		 if (SpecificationManager.checkSpecification(8)) {
			 Floor[] floors = e.getEnv().getFloors();
			 if (floorButtonPressed == null || floors.length != floorButtonPressed.length)
				 floorButtonPressed = new boolean[floors.length];
			 for (int i = 0; i < floors.length; i++) {
				 if (floors[i].hasCall()) floorButtonPressed[i]= true;
				 else floorButtonPressed[i]= false;
			 }
			 wasEmptyBeforeTimeStep = e.isEmpty();
		 }
	 }
	 after(Elevator e) : timeShift(e) {
		 if (SpecificationManager.checkSpecification(8))
			 if (e.areDoorsOpen() && wasEmptyBeforeTimeStep && !floorButtonPressed[e.getCurrentFloorID()]) {
				 failure(new SpecificationException("Spec8","(Spec8) Empty Lift stopped at Floor " + e.getCurrentFloorID() + " although the FloorButton was not pressed."));
			 }
	 }
	 // specification 9
	 /*
	  * The Lift will honor Requests from within the lift as long as it is not empty.
	  * (this is actually a copy of Spec2 with added property that the lift is not empty.
	  */
		boolean[] calledAt_Spec9;
		// initialization
		before(int numFloors) : 
			call(ElevatorSystem.Environment.new(int)) && args(numFloors) {
				if (SpecificationManager.checkSpecification(9))
					calledAt_Spec9 = new boolean[numFloors];
	     	}
		// collect all pressed buttons
		 before(int floorID) : 
			call(public void ElevatorSystem.Elevator.pressInLiftFloorButton(int)) && args(floorID) {
			 	if (SpecificationManager.checkSpecification(9))
			 		calledAt_Spec9[floorID] = true;
	     	}
		// monitor if the floors are visited
		 after(Elevator e) : 
			call(public void ElevatorSystem.Elevator.timeShift()) && target(e) {
			 if (SpecificationManager.checkSpecification(9)) {
				 int floor = e.getCurrentFloorID();
				 if (e.isEmpty()) Arrays.fill(calledAt_Spec9, false); // this is the difference to Spec2
				 else if (calledAt_Spec9[floor] && e.areDoorsOpen()) {
					 calledAt_Spec9[floor] = false; // reset
				 }
			 }
	     	}
		 // fail if some floors were not visited in the end
		 after() : programTermination() {
			 	//printArrayReverse(calledAt_Spec9);
			 if (SpecificationManager.checkSpecification(9))
				for (int i = 0; i < calledAt_Spec9.length; i++) {
					if (calledAt_Spec9[i]==true) failure(new SpecificationException("Spec9","(Spec9) (not-empty) Elevator did not stop at Floor" + i + " as requested (from inside, not empty)"));
				}
		 }
}
