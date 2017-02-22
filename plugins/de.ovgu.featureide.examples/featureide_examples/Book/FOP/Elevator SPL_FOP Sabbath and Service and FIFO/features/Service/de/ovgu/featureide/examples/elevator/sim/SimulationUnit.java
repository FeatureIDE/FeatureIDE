package de.ovgu.featureide.examples.elevator.sim;

public class SimulationUnit {

	private static MainWindow createMainWindow(SimulationUnit sim) { 
		return new MainWindow(sim); 
	}

	public boolean toggleService() {
		return controller.toggleService();
	}
	
}