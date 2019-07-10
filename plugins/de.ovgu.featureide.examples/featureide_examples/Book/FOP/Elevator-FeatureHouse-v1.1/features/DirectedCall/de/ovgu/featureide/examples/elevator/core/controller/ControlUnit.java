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

	private RequestComparator comparator =
		new Request.UpComparator(this);
	private RequestComparator downComparator =
		new Request.DownComparator(this);
	private PriorityBlockingQueue<Request> q =
		new PriorityBlockingQueue<Request>(1, new Request.UpComparator(this));

	private ElevatorState setNextState() {
		ElevatorState state =
			original();
		sortQueue();
		return state;
	}

	private void sortQueue() {
		final ElevatorState direction =
			elevator.getCurrentState();
		final PriorityBlockingQueue<Request> pQueue;
		switch (direction) {
		case MOVING_DOWN:
			pQueue =
				new PriorityBlockingQueue<Request>(Math.max(1, q.size()), downComparator);
			break;
		case MOVING_UP:
			pQueue =
				new PriorityBlockingQueue<Request>(Math.max(1, q.size()), comparator);
			break;
		default:
			return;
		}
		q.drainTo(pQueue);
		q =
			pQueue;
	}
}
