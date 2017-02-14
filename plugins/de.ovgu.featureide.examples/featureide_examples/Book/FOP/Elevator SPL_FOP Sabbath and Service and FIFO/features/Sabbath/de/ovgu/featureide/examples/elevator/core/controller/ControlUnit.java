package de.ovgu.featureide.examples.elevator.core.controller;

import de.ovgu.featureide.examples.elevator.core.model.ElevatorState;

/**
 * TODO description
 */
public class ControlUnit {

	private ElevatorState calculateNextState() {
		final int currentFloor = elevator.getCurrentFloor();
		switch (elevator.getCurrentState()) {
		case FLOORING:
			switch (elevator.getDirection()) {
			case MOVING_DOWN:
				return (currentFloor <= elevator.getMinFloor()) ? ElevatorState.MOVING_UP : ElevatorState.MOVING_DOWN;
			case MOVING_UP:
				return (currentFloor >= elevator.getMaxFloor()) ? ElevatorState.MOVING_DOWN : ElevatorState.MOVING_UP;
			default:
				return ElevatorState.MOVING_UP;
			}
		}
		return original();
	}
	
}