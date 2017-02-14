package de.ovgu.featureide.examples.elevator.sim;

import java.text.SimpleDateFormat;
import java.util.Date;

import de.ovgu.featureide.examples.elevator.core.controller.ControlUnit;
import de.ovgu.featureide.examples.elevator.core.controller.ITickListener;
import de.ovgu.featureide.examples.elevator.core.controller.Request;
import de.ovgu.featureide.examples.elevator.core.model.Elevator;
import de.ovgu.featureide.examples.elevator.ui.MainWindow;

public class SimulationUnit {

		
	private static MainWindow simulationWindow;
	private ControlUnit controller;
	
	public static void main(String[] args) {
		SimulationUnit sim = new SimulationUnit();
		//#if Service | FIFO
		simulationWindow = new MainWindow(sim);
		//#else
//@		simulationWindow = new MainWindow();
		//#endif
		sim.start(5);
	}
	
	public void start(int maxFloor) {
		Elevator elevator = new Elevator(maxFloor);
		controller = new ControlUnit(elevator);
		
		Thread controllerThread = new Thread(controller);
		controller.addTickListener(new ITickListener() {
			public void onTick(Elevator elevator) {
				System.out.printf(String.format("%s - %s -- Current Floor %d \n", new SimpleDateFormat("HH:mm:ss").format(new Date()),
						elevator.getCurrentState(), elevator.getCurrentFloor()));
			}

			//#if FIFO
			@Override
			public void onRequestFinished(Elevator elevator, Request request) {
				
			}
			//#endif
		});
		controller.addTickListener(simulationWindow);
		
		simulationWindow.initialize(elevator.getMaxFloor());
		controllerThread.start();
	}

	//#if Service
	public boolean toggleService() {
		return controller.toggleService();
	}
	//#endif
	
	// #if FIFO
	public void floorRequest(Request floorRequest) {
		controller.trigger(floorRequest);
	}

	public int getCurrentFloor() {
		return controller.getCurrentFloor();
	}
	// #endif

	
}
