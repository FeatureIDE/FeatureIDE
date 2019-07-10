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
import de.ovgu.featureide.examples.elevator.core.model.ElevatorState;

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
	private JToggleButton btnFloorUp, btnFloorDown;

	public FloorComposite(boolean showsOpen, int level, SimulationUnit sim, boolean isMaxLevel) {
		this.level =
			level;
		this.simulation =
			sim;
		setUpFloor(showsOpen, level, isMaxLevel);
	}

	private void setUpFloor(boolean showsOpen, int level, boolean isMaxLevel) {
		this.setUpFloor(showsOpen, level);
		if (!isMaxLevel) {
			add(Box.createRigidArea(new Dimension(5, 0)));
			btnFloorUp =
				new JToggleButton();
			btnFloorUp.setIcon(new ImageIcon(FloorComposite.class.getResource("/arrow_up_small.png")));
			btnFloorUp.setActionCommand("UP");
			btnFloorUp.addActionListener(this);
			add(btnFloorUp);
		}

		if (level != 0) {
			add(Box.createRigidArea(new Dimension(5, 0)));
			btnFloorDown =
				new JToggleButton();
			btnFloorDown.setIcon(new ImageIcon(FloorComposite.class.getResource("/arrow_down_small.png")));
			btnFloorDown.setActionCommand("DOWN");
			btnFloorDown.addActionListener(this);
			add(btnFloorDown);
		}
	}

	private void setPermitted(boolean isEnabled) {
		original(isEnabled);
		if (btnFloorUp != null) btnFloorUp.setEnabled(isEnabled);
		if (btnFloorDown != null) btnFloorDown.setEnabled(isEnabled);
	}

	public boolean isFloorRequested() {
		if (btnFloorUp != null
			&& !btnFloorUp.isEnabled() && btnFloorUp.isSelected()) {
			return true;
		}
		if (btnFloorDown != null
			&& !btnFloorDown.isEnabled() && btnFloorDown.isSelected()) {
			return true;
		}
		return original();
	}

	public void resetFloorRequest() {
		resetUp();
		resetDown();
	}

	public void resetUp() {
		if (btnFloorUp != null
			&& !btnFloorUp.isEnabled()) {
			btnFloorUp.setSelected(false);
			btnFloorUp.setEnabled(true);
		}
	}

	public void resetDown() {
		if (btnFloorDown != null
			&& !btnFloorDown.isEnabled()) {
			btnFloorDown.setSelected(false);
			btnFloorDown.setEnabled(true);
		}
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		if (simulation.getCurrentFloor() != level) {
			String actionCmd =
				e.getActionCommand();
			if ("UP".equals(actionCmd)) {
				simulation.floorRequest(new Request(level, ElevatorState.MOVING_UP));
				btnFloorUp.setEnabled(false);
				btnFloorUp.setSelected(true);
			} else {
				simulation.floorRequest(new Request(level, ElevatorState.MOVING_DOWN));
				btnFloorDown.setEnabled(false);
				btnFloorDown.setSelected(true);
			}
		} else {
			if (btnFloorDown != null) btnFloorDown.setSelected(false);
			if (btnFloorUp != null) btnFloorUp.setSelected(false);
		}
	}

}
