package de.ovgu.featureide.examples.elevator.sim;

import java.text.SimpleDateFormat;
import java.util.Date;
//#if FloorPermission
import java.util.List;
//#endif

import de.ovgu.featureide.examples.elevator.core.controller.ControlUnit;
import de.ovgu.featureide.examples.elevator.core.controller.ITickListener;
//#if CallButtons
import de.ovgu.featureide.examples.elevator.core.controller.ITriggerListener;
import de.ovgu.featureide.examples.elevator.core.controller.Request;
//#endif
import de.ovgu.featureide.examples.elevator.core.model.Elevator;
import de.ovgu.featureide.examples.elevator.ui.MainWindow;

public class SimulationUnit {

	//#if CallButtons
	private ITriggerListener triggerListener;
	//#endif
	private static MainWindow simulationWindow;
	private ControlUnit controller;
	
	public static void main(String[] args) {
		SimulationUnit sim = new SimulationUnit();
		//#if CallButtons | FloorPermission | Service
		simulationWindow = new MainWindow(sim);
		//#else
//@		simulationWindow = new MainWindow();
		//#endif
		sim.start(5);
	}
	
	public void start(int maxFloor) {
		Elevator elevator = new Elevator(maxFloor);
		controller = new ControlUnit(elevator);
		//#if CallButtons
		this.setTriggerListener(controller);
		//#endif
		
		Thread controllerThread = new Thread(controller);
		controller.addTickListener(new ITickListener() {
			public void onTick(Elevator elevator) {
				System.out.printf(String.format("%s - %s -- Current Floor %d Next Floor %d \n", new SimpleDateFormat("HH:mm:ss").format(new Date()),
						elevator.getCurrentState(), elevator.getCurrentFloor(), Integer.MAX_VALUE));
			}
			//#if CallButtons
			@Override
			public void onRequestFinished(Elevator elevator, Request request) {				
			}
			//#endif
		});
		controller.addTickListener(simulationWindow);
		
		simulationWindow.initialize(elevator.getMaxFloor());
		controllerThread.start();
	}
	
	//#if CallButtons
	/**
	 * The simulation unit is a bridge between gui and control unit.
	 * So there is a need to delegate requests made by the gui to the control unit.
	 * Thats why the simulationunit is also capable of informing trigger listener.
	 * @param listener - The trigger listener.
	 */
	public void setTriggerListener(ITriggerListener listener) {
		this.triggerListener = listener;
	}
	//#endif

	//#if CallButtons
	/**
	 * Send a floor request to the trigger listener.
	 * @param floorRequest -  The floor request to send to the trigger listener.
	 */
	public void floorRequest(Request floorRequest) {
		this.triggerListener.trigger(floorRequest);		
	}
	
	public int getCurrentFloor() {
		return controller.getCurrentFloor();
	}
	//#endif
	
	//#if Service
	public void toggleService() {
		controller.setService(!controller.isInService());
	}
		
	public boolean isInService() {
		return controller.isInService();
	}
	//#endif

	//#if FloorPermission
	public void setDisabledFloors(List<Integer> disabledFloors) {
		this.controller.setDisabledFloors(disabledFloors);
	}
	
	public List<Integer> getDisabledFloors() {
		return this.controller.getDisabledFloors();
	}
	
	public boolean isDisabledFloor(int level) {
		return this.controller.isDisabledFloor(level);
	}
	//#endif
}
