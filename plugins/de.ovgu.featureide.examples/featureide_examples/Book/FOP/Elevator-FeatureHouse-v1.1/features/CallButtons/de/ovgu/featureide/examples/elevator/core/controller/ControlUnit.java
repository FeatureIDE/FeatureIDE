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
import java.util.concurrent.PriorityBlockingQueue;

import de.ovgu.featureide.examples.elevator.core.model.Elevator;
import de.ovgu.featureide.examples.elevator.core.model.ElevatorState;
import de.ovgu.featureide.examples.elevator.core.controller.Request;
import de.ovgu.featureide.examples.elevator.core.controller.Request.RequestComparator;

/**
 * 
 * This class controls the elevator.
 * 
 * @author FeatureIDE Team
 */
public class ControlUnit implements ITriggerListener {

	private static final Object calc =
		new Object();
	private PriorityBlockingQueue<Request> q =
		new PriorityBlockingQueue<Request>(1);

	private ElevatorState setNextState() {
		synchronized (calc) {
			return original();
		}
	}

	private ElevatorState calculateNextState() {
		final int currentFloor =
			elevator.getCurrentFloor();
		return getElevatorState(currentFloor);
	}

	private ElevatorState getElevatorState(int currentFloor) {
		if (!q.isEmpty()) {
			Request poll =
				q.peek();
			int floor =
				poll.getFloor();
			if (floor == currentFloor) {
				do {
					triggerOnRequest(q.poll());
					poll =
						q.peek();
				} while (poll != null
					&& poll.getFloor() == currentFloor);
				return ElevatorState.FLOORING;
			} else if (floor > currentFloor) {
				return ElevatorState.MOVING_UP;
			} else {
				return ElevatorState.MOVING_DOWN;
			}
		}
		return ElevatorState.FLOORING;
	}

	private void triggerOnRequest(Request request) {
		for (ITickListener listener : this.tickListener) {
			listener.onRequestFinished(elevator, request);
		}
	}

	@Override
	public void trigger(Request req) {
		synchronized (calc) {
			q.offer(req);
		}
	}

	public int getCurrentFloor() {
		return elevator.getCurrentFloor();
	}

}
