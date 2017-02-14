package de.ovgu.featureide.examples.elevator.sim;

import de.ovgu.featureide.examples.elevator.core.controller.Request;

public class SimulationUnit {

	private static class ConsoleListener implements ITickListener {
		public void onRequestFinished(Elevator e, Request r) {}
	}

	private static MainWindow createMainWindow(SimulationUnit sim) {
		return new MainWindow(sim);
	}

	public void floorRequest(Request floorRequest) {
		controller.trigger(floorRequest);
	}

	public int getCurrentFloor() {
		return controller.getCurrentFloor();
	}
	
}