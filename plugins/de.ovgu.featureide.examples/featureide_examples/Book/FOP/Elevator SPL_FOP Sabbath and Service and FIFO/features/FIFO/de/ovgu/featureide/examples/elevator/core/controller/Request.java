package de.ovgu.featureide.examples.elevator.core.controller;

public class Request {
	
	private int floor;

	public int getFloor() { 
		return floor; 
	}

	public Request(int floor) {
		this.floor = floor; 
	}
	
	public boolean equals(Object other) {
		return ((Request)other).floor == floor;
	}
	
}