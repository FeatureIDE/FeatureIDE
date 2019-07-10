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
package de.ovgu.featureide.examples.elevator.core.controller;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.examples.elevator.core.model.Elevator;
import de.ovgu.featureide.examples.elevator.core.model.ElevatorState;

/**
 * 
 * This class controls the elevator.
 * 
 * @author FeatureIDE Team
 */
public class ControlUnit implements Runnable {

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
		default:
			return null;
		}
	}
}
