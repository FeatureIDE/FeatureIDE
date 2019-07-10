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
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.Box;
import javax.swing.JToggleButton;
import de.ovgu.featureide.examples.elevator.core.controller.Request;

import javax.swing.BoxLayout;
import javax.swing.ImageIcon;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.SwingConstants;
import javax.swing.SwingUtilities;
import javax.swing.border.EmptyBorder;

import de.ovgu.featureide.examples.elevator.sim.SimulationUnit;

/**
 * 
 * This class creates a floor on the window.
 * 
 * @author FeatureIDE Team
 */
public class FloorComposite extends JPanel implements ActionListener {

	private int level;
	private SimulationUnit simulation;
	private JToggleButton btnFloorRequest = new JToggleButton();;

	public FloorComposite(boolean showsOpen, int level, SimulationUnit sim) {
		this(showsOpen, level);
		this.level = level;
		this.simulation = sim;
		add(Box.createRigidArea(new Dimension(5, 0)));
		btnFloorRequest.setIcon(new ImageIcon(FloorComposite.class.getResource("/circle_small.png")));
		btnFloorRequest.setActionCommand(String.valueOf(level));
		btnFloorRequest.addActionListener(this);
		add(btnFloorRequest);
	}

	public boolean isFloorRequested() {
		if (!btnFloorRequest.isEnabled() && btnFloorRequest.isSelected()) {
			return true;
		}
		return false;
	}

	public void resetFloorRequest() {
		if (!btnFloorRequest.isEnabled()) {
			btnFloorRequest.setSelected(false);
			btnFloorRequest.setEnabled(true);
		}
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		if (simulation.getCurrentFloor() != level) {
			simulation.floorRequest(new Request(level));
			btnFloorRequest.setEnabled(false);
			btnFloorRequest.setSelected(true);
		} else {
			if (btnFloorRequest != null)
				btnFloorRequest.setSelected(false);
		}
	}

}
