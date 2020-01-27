/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
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
