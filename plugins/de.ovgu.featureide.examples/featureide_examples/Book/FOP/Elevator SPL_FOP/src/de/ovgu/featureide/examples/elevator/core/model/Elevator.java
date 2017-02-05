
package de.ovgu.featureide.examples.elevator.core.model;

public class Elevator {
	
	private final int maxFloor;
	private final int minFloor = 0;

	private ElevatorState direction = ElevatorState.MOVING_UP; 

	private int currentFloor = 0;
	private ElevatorState currentState = ElevatorState.FLOORING;
	
	public Elevator(int maxFloor) { this.maxFloor = maxFloor; }
	
	public int getMaxFloor() { return maxFloor;	}
	public int getMinFloor() { return minFloor; }
	
	public ElevatorState getDirection() { return direction; }
	public void setDirection(ElevatorState direction) { this.direction = direction; }
	
	public void setCurrentFloor(int currentFloor) { this.currentFloor = currentFloor; }
	public int getCurrentFloor() { return currentFloor; }
	 
	public ElevatorState getCurrentState() { return currentState; }
	public void setCurrentState(ElevatorState state) { currentState = state; }
}
