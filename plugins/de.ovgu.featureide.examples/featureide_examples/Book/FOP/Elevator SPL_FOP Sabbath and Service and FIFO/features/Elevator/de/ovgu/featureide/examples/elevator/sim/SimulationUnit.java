package de.ovgu.featureide.examples.elevator.sim;

import java.text.SimpleDateFormat;
import java.util.Date;

import de.ovgu.featureide.examples.elevator.core.controller.ControlUnit;
import de.ovgu.featureide.examples.elevator.core.controller.ITickListener;
import de.ovgu.featureide.examples.elevator.core.model.Elevator;
import de.ovgu.featureide.examples.elevator.ui.MainWindow;

public class SimulationUnit {

	private static MainWindow simulationWindow;
	private ControlUnit controller;
	
	public static void main(String[] args) {
		SimulationUnit sim = new SimulationUnit();
		simulationWindow = createMainWindow(sim);
		sim.start(5);
	}
	
	private static MainWindow createMainWindow(SimulationUnit sim) {
		return new MainWindow();
	}
	
	public void start(int maxFloor) {
		Elevator elevator = new Elevator(maxFloor);
		controller = new ControlUnit(elevator);
		
		Thread controllerThread = new Thread(controller);
		controller.addTickListener(new ConsoleListener());
		controller.addTickListener(simulationWindow);
		
		simulationWindow.initialize(elevator.getMaxFloor());
		controllerThread.start();
	}
	
	private static class ConsoleListener implements ITickListener {
		public void onTick(Elevator elevator) {
			System.out.printf(String.format("%s - %s -- Current Floor %d \n", new SimpleDateFormat("HH:mm:ss").format(new Date()),
					elevator.getCurrentState(), elevator.getCurrentFloor()));
		}
	}
	
}
