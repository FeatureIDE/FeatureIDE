package de.ovgu.featureide.examples.elevator.core.controller;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import de.ovgu.featureide.examples.elevator.core.model.Elevator;
import de.ovgu.featureide.examples.elevator.core.model.ElevatorState;

public class ControlUnit implements Runnable 
//#if FIFO
, ITriggerListener
//#endif
{
	
	public static int TIME_DELAY = 700;
	public boolean run = true;

	private Elevator elevator;
	
	public ControlUnit(Elevator elevator) {
		this.elevator = elevator;
	}
	
	// #if FIFO
	private Queue<Request> requests = new LinkedList<>();
	// #endif

	public void run() {
		while (run) {
			final ElevatorState state;
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
		if (elevator.isInService()) {
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
//@		}
		//#endif
		
		// #if FIFO
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
		// #endif
		return ElevatorState.FLOORING;
	}
	
	//#if FIFO
	private void requestFinished(Request request) {
		for (ITickListener listener : this.tickListener) {
			listener.onRequestFinished(elevator, request);
		}
	}
	public int getCurrentFloor() {
		return elevator.getCurrentFloor();
	}
	//#endif
	
	//#if Service
	public boolean toggleService() {
		elevator.setInService(!elevator.isInService());
		return elevator.isInService();
	}
	//#endif

	private List<ITickListener> tickListener = new ArrayList<ITickListener>();


	public void addTickListener(ITickListener ticker) {
		this.tickListener.add(ticker);
	}

	private void triggerOnTick() {
		for (ITickListener listener : this.tickListener) {
			listener.onTick(elevator);
		}
	}

	//#if FIFO
	@Override
	public void trigger(Request request) {
		if (!requests.contains(request)) {
			requests.offer(request);
		}
	}
	//#endif
}
