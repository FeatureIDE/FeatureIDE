package de.ovgu.featureide.examples.elevator.core.model;

public class Elevator {

	private boolean inService = false;
	
	public void setService(boolean mode) {
		this.inService = mode;
	}
	
	public boolean isInService() {
		return inService;
	}
	
}