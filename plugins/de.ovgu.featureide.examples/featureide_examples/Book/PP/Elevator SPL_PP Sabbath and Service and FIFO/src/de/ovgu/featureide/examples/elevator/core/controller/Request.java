//#condition FIFO
package de.ovgu.featureide.examples.elevator.core.controller;

public class Request {

	private final int floor;

	public Request(int floor) {
		this.floor = floor;
	}
	
	public int getFloor() {
		return floor;
	}
	
	@Override
	public boolean equals(Object other) {
		return ((Request)other).floor == floor;
	}
}
