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
package de.ovgu.featureide.examples.elevator.ui;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;

import de.ovgu.featureide.examples.elevator.sim.SimulationUnit;

import javax.swing.BoxLayout;
import javax.swing.ImageIcon;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.SwingConstants;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;
import javax.swing.border.EmptyBorder;

/**
 * 
 * This class creates a floor on the window.
 * 
 * @author FeatureIDE Team
 */
public class FloorComposite {

	private SimulationUnit simulation;
	private boolean isEnabled =
		true;

	public FloorComposite(boolean showsOpen, int level, SimulationUnit sim) {
		if (simulation == null) {
			this.simulation =
				sim;
			setUpFloor(showsOpen, level);
		}
	}

	private void setUpFloor(boolean showsOpen, int level) {
		original(showsOpen, level);
		this.isEnabled =
			simulation.isDisabledFloor(level);
		setPermitted(isEnabled);
	}

	private void changeImage() {
		if (isEnabled)
			original();
	}

}
