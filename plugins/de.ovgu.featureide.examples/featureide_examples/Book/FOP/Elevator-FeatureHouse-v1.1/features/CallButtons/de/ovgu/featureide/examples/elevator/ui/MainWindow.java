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
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.GridLayout;
import java.awt.Insets;
import java.awt.event.*;
import java.util.ArrayList;
import java.util.List;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.ScrollPaneConstants;
import javax.swing.JToggleButton;

import de.ovgu.featureide.examples.elevator.core.controller.ITickListener;
import de.ovgu.featureide.examples.elevator.core.controller.Request;
import de.ovgu.featureide.examples.elevator.sim.SimulationUnit;

/**
 * 
 * This class implements a panel with background.
 * 
 * @author FeatureIDE Team
 */
public class MainWindow implements ActionListener {

	private SimulationUnit sim;
	private List<JToggleButton> listInnerElevatorControls =
		new ArrayList<JToggleButton>();

	public MainWindow(SimulationUnit sim) {
		this.sim =
			sim;
	}

	private void addElevatorControlButtons() {
		original();
		JPanel panel_floors =
			new JPanel(new GridLayout(0, 3));
		panel_floors.setBackground(Color.GRAY);

		JToggleButton btnFloor;
		for (int i =
			maxFloors; i >= 0; i--) {
			btnFloor =
				new JToggleButton(String.valueOf(i));
			btnFloor.setActionCommand(String.valueOf(i));
			btnFloor.addActionListener(this);
			panel_floors.add(btnFloor);
			listInnerElevatorControls.add(0, btnFloor);
		}

		GridBagConstraints gbc_btnFloor =
			new GridBagConstraints();
		gbc_btnFloor.insets =
			new Insets(0, 0, 0, 0);
		gbc_btnFloor.fill =
			GridBagConstraints.BOTH;
		gbc_btnFloor.gridwidth =
			4;
		gbc_btnFloor.gridx =
			2;
		gbc_btnFloor.gridy =
			4;

		((JPanel) splitPane.getRightComponent()).add(panel_floors, gbc_btnFloor);
	}

	private FloorComposite createFloorComposite(int floor) {
		return new FloorComposite(floor == 0, floor, sim);
	}

	private void runFlooringTasks(int currentFloor) {
		original(currentFloor);
		JToggleButton btnFloor =
			listInnerElevatorControls.get(currentFloor);
		if (btnFloor.isSelected()) {
			btnFloor.setSelected(false);
			btnFloor.setEnabled(true);
		}
	}

	@Override
	public void onRequestFinished(Elevator elevator, Request request) {
		listFloorComposites.get(request.getFloor()).resetFloorRequest();
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		sim.floorRequest(new Request(Integer.valueOf(e.getActionCommand())));
		listInnerElevatorControls.get(Integer.valueOf(e.getActionCommand())).setEnabled(false);
	}

}
