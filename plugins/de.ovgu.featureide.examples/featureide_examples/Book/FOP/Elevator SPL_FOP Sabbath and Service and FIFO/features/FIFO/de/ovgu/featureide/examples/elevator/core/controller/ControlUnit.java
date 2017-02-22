package de.ovgu.featureide.examples.elevator.core.controller;

import java.util.LinkedList;
import java.util.Queue;

public class ControlUnit {

	private Queue<Request> requests = new LinkedList<Request>();

	public void trigger(Request request) {
		if (!requests.contains(request)) {
			requests.offer(request);
		}
	}

	private ElevatorState calculateNextState() {
		final int currentFloor = elevator.getCurrentFloor();
		if (!requests.isEmpty()) {
			Request nextRequest = requests.peek();
			int floor = nextRequest.getFloor();
			if (floor > currentFloor) {
				return ElevatorState.MOVING_UP;
			} else if (floor < currentFloor) {
				return ElevatorState.MOVING_DOWN;
			} else {
				requestFinished(requests.poll());
				return ElevatorState.FLOORING;
			}
		}
		return original();
	}

	private void requestFinished(Request request) {
		for (ITickListener listener : this.tickListener) {
			listener.onRequestFinished(elevator, request);
		}
	}

	public int getCurrentFloor() {
		return elevator.getCurrentFloor();
	}

}