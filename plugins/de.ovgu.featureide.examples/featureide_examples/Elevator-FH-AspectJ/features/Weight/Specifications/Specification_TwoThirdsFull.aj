package Specifications;

import ElevatorSystem.Elevator;
import TestSpecifications.SpecificationException;
import TestSpecifications.SpecificationManager;

public privileged aspect Specification_TwoThirdsFull extends AbstractSpecification {
	// specification 13
	// Car calls have precedence when the Lift is two thirds full.
	 pointcut timeShift(Elevator e) : execution(public void ElevatorSystem.Elevator.timeShift()) && target(e);
	 pointcut continueInDirection(Elevator e) : execution(private void ElevatorSystem.Elevator.continueInDirection(ElevatorSystem.Elevator.Direction)) && target(e);
	 
	 Elevator.Direction prevDir;
	 int prevFloor=0;
	 before(Elevator e) : continueInDirection(e) {
		 if (SpecificationManager.checkSpecification(13)) {
			 prevDir = e.getCurrentDirection();
			 prevFloor = e.getCurrentFloorID();
		 }
		 //System.out.println("prev:" + prevDir);
	 }
	 after(Elevator e) : continueInDirection(e) {
		 if (SpecificationManager.checkSpecification(13)) {
			 if (e.getCurrentFloorID()!= prevFloor) { // if it moved
				 if (e.weight > Elevator.maximumWeight*2/3) {
					 if (prevDir == Elevator.Direction.up) {
						 if (existInLiftCallsInDirection(Elevator.Direction.down, e) && 
							 !existInLiftCallsInDirection(Elevator.Direction.up, e))
							 if (e.getCurrentDirection() == Elevator.Direction.up)
								 failure(new SpecificationException("Spec13","(Spec13) Did not give precedence to in-Lift-Button although > 2/3 of maxWeight (going up from " + e.getCurrentFloorID() + ")"));
					 } else if (prevDir == Elevator.Direction.down) {
						 if (existInLiftCallsInDirection(Elevator.Direction.up, e) && 
							 !existInLiftCallsInDirection(Elevator.Direction.down, e))
							 if (e.getCurrentDirection() == Elevator.Direction.down)
								 failure(new SpecificationException("Spec13","(Spec13) Did not give precedence to in-Lift-Button although > 2/3 of maxWeight (going down from " + e.getCurrentFloorID() + ")"));
					 }
				 }
			 }
		 }
	 }
	 
	 private boolean existInLiftCallsInDirection(Elevator.Direction d, Elevator e) {
		 if (d == Elevator.Direction.up) {
			 for (int i =  e.getCurrentFloorID(); i < e.floorButtons.length; i++)
				 if (e.buttonForFloorIsPressed(i)) return true;
		 } else if (d == Elevator.Direction.down) {
			 for (int i =  e.getCurrentFloorID(); i >= 0; i--)
				 if (e.buttonForFloorIsPressed(i)) return true;
		 }
		 return false;		 
	 }
}
