package de.ovgu.featureide.examples.elevator.core.controller;

public interface ITickListener {
	void onRequestFinished(Elevator elevator, Request request);
}