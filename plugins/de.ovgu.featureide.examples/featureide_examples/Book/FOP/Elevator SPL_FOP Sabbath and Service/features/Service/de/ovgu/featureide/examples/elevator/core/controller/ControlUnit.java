package de.ovgu.featureide.examples.elevator.core.controller;

public class ControlUnit {

	private ElevatorState calculateNextState() {
		final int currentFloor = elevator.getCurrentFloor();
		if (elevator.isInService()) {
			if (currentFloor != elevator.getMinFloor()) {
				return ElevatorState.MOVING_DOWN;
			} else {
				return ElevatorState.FLOORING;
			}
		}
		return original();
	}

	public boolean toggleService() {
		elevator.setService(!elevator.isInService());
		return elevator.isInService();
	}
	
}