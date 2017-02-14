package de.ovgu.featureide.examples.elevator.core.controller;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.examples.elevator.core.model.Elevator;
import de.ovgu.featureide.examples.elevator.core.model.ElevatorState;

/**
 * Controller of the elevator.
 */
public class ControlUnit implements Runnable {
	
	public static int TIME_DELAY = 700;
	public boolean run = true;

	private Elevator elevator;
	
	public ControlUnit(Elevator elevator) {
		this.elevator = elevator;
	}

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
		return ElevatorState.FLOORING;
	}

	private List<ITickListener> tickListener = new ArrayList<ITickListener>();


	public void addTickListener(ITickListener ticker) {
		this.tickListener.add(ticker);
	}

	private void triggerOnTick() {
		for (ITickListener listener : this.tickListener) {
			listener.onTick(elevator);
		}
	}
}
