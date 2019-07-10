/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

/**
 * 
 * This class represents the elevator.
 * 
 * @author FeatureIDE Team
 */
public class Elevator {

	private final int maxFloor;
	private final int minFloor =
		0;

	private ElevatorState direction =
		ElevatorState.MOVING_UP;

	private int currentFloor =
		0;
	private ElevatorState currentState =
		ElevatorState.FLOORING;

	public Elevator(int maxFloor) {
		this.maxFloor =
			maxFloor;
	}

	public int getMaxFloor() {
		return maxFloor;
	}

	public int getMinFloor() {
		return minFloor;
	}

	public ElevatorState getDirection() {
		return direction;
	}

	public void setDirection(ElevatorState direction) {
		this.direction =
			direction;
	}

	public void setCurrentFloor(int currentFloor) {
		this.currentFloor =
			currentFloor;
	}

	public int getCurrentFloor() {
		return currentFloor;
	}

	public ElevatorState getCurrentState() {
		return currentState;
	}

	public void setCurrentState(ElevatorState state) {
		currentState =
			state;
	}
}
