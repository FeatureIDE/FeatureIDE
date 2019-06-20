/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.examples.elevator.ui;

import java.awt.Component;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import javax.swing.JPanel;
import javax.swing.JToggleButton;

import de.ovgu.featureide.examples.elevator.sim.SimulationUnit;

/**
 * 
 * This class implements a panel with background.
 * 
 * @author FeatureIDE Team
 */
public class MainWindow {

	private SimulationUnit sim;

	public MainWindow(SimulationUnit sim) {
		this.sim =
			sim;
	}

	public void initialize(int maxFloors) {
		FloorChooseDialog permissionDialog =
			new FloorChooseDialog(maxFloors, Arrays.asList(0),
					"Choose disabled floors");
		List<Integer> disabledFloors =
			permissionDialog.getSelectedFloors();
		sim.setDisabledFloors(disabledFloors);
		permissionDialog.dispose();
		original(maxFloors);
	}

	private void addElevatorControlButtons() {
		original();
		JPanel panel =
			((JPanel) splitPane.getRightComponent());
		for (Component c : panel.getComponents()) {
			if (c instanceof JPanel) {
				for (Component tb : ((JPanel) c).getComponents()) {
					if (tb instanceof JToggleButton) {
						if (!((JToggleButton) tb).getText().equals("Service")) {
							tb.setEnabled(sim.isDisabledFloor(Integer.parseInt(((JToggleButton) tb).getText())));
						}
					}
				}
			}
		}
	}

	private FloorComposite createFloorComposite(int floor) {
		return new FloorComposite(floor == 0, floor, sim);
	}

}
