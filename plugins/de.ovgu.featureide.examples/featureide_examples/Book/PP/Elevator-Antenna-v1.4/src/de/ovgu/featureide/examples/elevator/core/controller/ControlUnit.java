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
package de.ovgu.featureide.examples.elevator.core.controller;

import java.util.ArrayList;
import java.util.List;

//#if CallButtons
import java.util.concurrent.PriorityBlockingQueue;
import de.ovgu.featureide.examples.elevator.core.controller.Request.RequestComparator;
//#endif

import de.ovgu.featureide.examples.elevator.core.model.Elevator;
import de.ovgu.featureide.examples.elevator.core.model.ElevatorState;

public class ControlUnit implements Runnable 
											//#if CallButtons
											, ITriggerListener
											//#endif
											{
	
	public static int TIME_DELAY = 700;
	public boolean run = true;

	private Elevator elevator;
	
	//#if CallButtons
	private static final Object calc = new Object();
	//#if FIFO
//@	private RequestComparator comparator = new RequestComparator();
	//#elif DirectedCall
	private RequestComparator comparator = new Request.UpComparator(this);
	private RequestComparator downComparator = new Request.DownComparator(this);
	//#else
//@	private RequestComparator comparator = new RequestComparator(this);
	//#endif
	private PriorityBlockingQueue<Request> q = new PriorityBlockingQueue<>(1, comparator);
	//#endif
	
	public ControlUnit(Elevator elevator) {
		this.elevator = elevator;
	}

	public void run() {
		while (run) {
			final ElevatorState state;
			//#if CallButtons
			synchronized (calc) {
			//#endif
				// Get next state of the elevator			
				state = calculateNextState();
				elevator.setCurrentState(state);
				switch (state) {
				case MOVING_UP:
					elevator.setDirection(ElevatorState.MOVING_UP);
					elevator.setCurrentFloor(elevator.getCurrentFloor() + 1);
					break;
				case MOVING_DOWN:
					elevator.setDirection(ElevatorState.MOVING_DOWN);
					elevator.setCurrentFloor(elevator.getCurrentFloor() - 1);
					break;
				case FLOORING:
					this.triggerOnTick();
					break;
				}
				//#if DirectedCall
				sortQueue();
				//#endif
			//#if CallButtons
			}
			//#endif
			
			// Moving or Waiting
			try {
				Thread.sleep(TIME_DELAY);
			} catch (InterruptedException e) {
			}
			
			switch (state) {
			case MOVING_UP:
				this.triggerOnTick();
				break;
			case MOVING_DOWN:
				this.triggerOnTick();
				break;
			default:
				break;
			}
		}
	}

	private ElevatorState calculateNextState() {
		final int currentFloor = elevator.getCurrentFloor();
		//#if Service
		if (isInService()) {
			if (currentFloor != elevator.getMinFloor()) {
				return ElevatorState.MOVING_DOWN;
			} else {
				return ElevatorState.FLOORING;
			}
		}
		//#endif
		//#if Sabbath
//@		switch (elevator.getCurrentState()) {
//@		case FLOORING:
//@			switch (elevator.getDirection()) {
//@			case MOVING_DOWN:
//@				return (currentFloor <= elevator.getMinFloor()) ? ElevatorState.MOVING_UP : ElevatorState.MOVING_DOWN;
//@			case MOVING_UP:
//@				return (currentFloor >= elevator.getMaxFloor()) ? ElevatorState.MOVING_DOWN : ElevatorState.MOVING_UP;
//@			default:
//@				return ElevatorState.MOVING_UP;
//@			}
//@		default:
//@			return ElevatorState.FLOORING;
//@		}
		//#endif
		//#if CallButtons
		return getElevatorState(currentFloor);
		//#endif
	}
	
	//#if CallButtons
	private ElevatorState getElevatorState(int currentFloor) {
		if (!q.isEmpty()) {
			Request poll = q.peek();
			int floor = poll.getFloor();
			if (floor == currentFloor) {
				do {
					triggerOnRequest(q.poll());
					poll = q.peek();
				} while (poll != null && poll.getFloor() == currentFloor);
				return ElevatorState.FLOORING;
			} else if (floor > currentFloor) {
				return ElevatorState.MOVING_UP;
			} else {
				return ElevatorState.MOVING_DOWN;
			}
		}
		return ElevatorState.FLOORING;
	}
	//#endif

	//#if DirectedCall
	private void sortQueue() {
		final ElevatorState direction = elevator.getCurrentState();
		final PriorityBlockingQueue<Request> pQueue;
		switch (direction) {
		case MOVING_DOWN:
			pQueue = new PriorityBlockingQueue<>(Math.max(1, q.size()), downComparator);
			break;
		case MOVING_UP:
			pQueue = new PriorityBlockingQueue<>(Math.max(1, q.size()), comparator);
			break;
		default:
			return;
		}
		q.drainTo(pQueue);
		q = pQueue;
	}
	//#endif

	private List<ITickListener> tickListener = new ArrayList<>();

	public void addTickListener(ITickListener ticker) {
		this.tickListener.add(ticker);
	}

	private void triggerOnTick() {
		for (ITickListener listener : this.tickListener) {
			listener.onTick(elevator);
		}
	}

	//#if CallButtons
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
	//#endif

	//#if Service
	public void setService(boolean modus) {
		elevator.setService(modus);
	}
		
	public boolean isInService() {
		return elevator.isInService();
	}
	//#endif

	//#if FloorPermission
	public void setDisabledFloors(List<Integer> disabledFloors) {
		elevator.setDisabledFloors(disabledFloors);
	}
	
	public List<Integer> getDisabledFloors() {
		return elevator.getDisabledFloors();
	}
	
	public boolean isDisabledFloor(int level) {
		return !elevator.getDisabledFloors().contains(level);
	}
	//#endif

}
