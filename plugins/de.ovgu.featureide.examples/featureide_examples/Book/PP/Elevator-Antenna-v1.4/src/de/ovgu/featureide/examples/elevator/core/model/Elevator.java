/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */

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
