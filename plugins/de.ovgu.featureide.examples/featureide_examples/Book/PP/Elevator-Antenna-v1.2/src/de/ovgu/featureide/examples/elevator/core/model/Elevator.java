
package de.ovgu.featureide.examples.elevator.core.model;

//#if FloorPermission
import java.util.List;
//#endif

public class Elevator {
	
	private final int maxFloor;
	private final int minFloor = 0;

	private ElevatorState direction = ElevatorState.MOVING_UP; 

	private int currentFloor = 0;
	private ElevatorState currentState = ElevatorState.FLOORING;
	
	//#if Service
	private boolean inService = false;
	//#endif
	
	//#if FloorPermission
	private List<Integer> disabledFloors;
	//#endif
	
	public Elevator(int maxFloor) { this.maxFloor = maxFloor; }
	
	public int getMaxFloor() { return maxFloor;	}
	public int getMinFloor() { return minFloor; }
	
	//#if Service
	public boolean isInService() { return inService; }
	public void setService(boolean inService) { this.inService = inService; }
	//#endif
	
	//#if FloorPermission
	public void setDisabledFloors(List<Integer> disabledFloors) { this.disabledFloors = disabledFloors; }
	public List<Integer> getDisabledFloors() { return this.disabledFloors; }
	//#endif
	
	public ElevatorState getDirection() { return direction; }
	public void setDirection(ElevatorState direction) { this.direction = direction; }
	
	public void setCurrentFloor(int currentFloor) { this.currentFloor = currentFloor; }
	public int getCurrentFloor() { return currentFloor; }
	 
	public ElevatorState getCurrentState() { return currentState; }
	public void setCurrentState(ElevatorState state) { currentState = state; }
}
