package Specifications;

import ElevatorSystem.Elevator;
import TestSpecifications.SpecificationException;
import TestSpecifications.SpecificationManager;

public privileged aspect Specification_ExecutiveFloor extends AbstractSpecification {
	// specification 14
	/* Original: The Lift will answer requests from the executive Floor.
	 * 
	 * My Version: While there is a request from the executive Floor the lift will not open its doors somewhere else.
	 * 
	 */
	 pointcut timeShift(Elevator e) : execution(public void ElevatorSystem.Elevator.timeShift()) && target(e);
	 
	 after(Elevator e) : timeShift(e) {
		 if (SpecificationManager.checkSpecification(14))
			 if (e.isExecutiveFloorCalling()) {
				if (! e.isExecutiveFloor(e.getCurrentFloorID()) && e.areDoorsOpen()) {
					if (SpecificationManager.checkSpecification(14))
					failure(new SpecificationException("Spec14","(Spec14) Opened the Doors at "+ e.getCurrentFloorID() + " although there was a call from the executive Suite."));
				}
			 }
	 }
}
