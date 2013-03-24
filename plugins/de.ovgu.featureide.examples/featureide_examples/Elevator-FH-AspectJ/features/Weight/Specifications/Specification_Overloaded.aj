package Specifications;

import ElevatorSystem.Elevator;
import TestSpecifications.SpecificationException;
import TestSpecifications.SpecificationManager;

public privileged aspect Specification_Overloaded extends AbstractSpecification {
	// specification 10
	/* Original: The Doors of the lift cannot be closed when the lift is overloaded.
	 * MyVersion: The doors are never closed when the lift is overloaded.
	 */
	 //pointcut allPublicElevatorMethods(Elevator e) : execution(public * ElevatorSystem.Elevator.*(..)) && target(e);

	 after(Elevator e) : timeShift(e) {
		 if (SpecificationManager.checkSpecification(10))
			 if (e.weight > Elevator.maximumWeight && !e.areDoorsOpen()) {
				 if (SpecificationManager.checkSpecification(10))
				 failure(new SpecificationException("Spec10","(Spec10) Doors are closed even though the Elevator is overloaded ("+e.weight + ">"+Elevator.maximumWeight+")"));
			 }
	 }
	 // specification 11
	 /* Elevator must not move while it is overloaded.
	  */
	 pointcut timeShift(Elevator e) : execution(public void ElevatorSystem.Elevator.timeShift()) && target(e);
	 int stayAt = -1000;
	 before(Elevator e) : timeShift(e) {
		 if (SpecificationManager.checkSpecification(11)) {
			 if (e.weight > Elevator.maximumWeight)
				 stayAt = e.getCurrentFloorID();
			 else 
				 stayAt = -1000;
		 }
	 }
	 after(Elevator e) : timeShift(e) {
		 if (SpecificationManager.checkSpecification(11))
			 if (stayAt != -1000 && stayAt != e.getCurrentFloorID()) {
				 if (SpecificationManager.checkSpecification(11))
				 failure(new SpecificationException("Spec11","(Spec11) Elevator moved from " + stayAt + " to "+ e.getCurrentFloorID() +" even though it is overloaded."));
			 }
	 }
}
