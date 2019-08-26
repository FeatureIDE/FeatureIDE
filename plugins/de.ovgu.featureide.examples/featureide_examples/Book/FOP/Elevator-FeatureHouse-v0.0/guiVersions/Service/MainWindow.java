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
import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JPanel;
import javax.swing.JToggleButton;

import de.ovgu.featureide.examples.elevator.sim.SimulationUnit;

/**
 * Extesnsion of the MainWindow for adding the service button.
 */
public class MainWindow {

	private SimulationUnit sim;

	public MainWindow(SimulationUnit sim) {
		this.sim = sim;
	}

	private void createPanelControlsContent(int maxFloors) {
		original(maxFloors);
		JToggleButton btnService = new JToggleButton("Service");
		btnService.setMinimumSize(new Dimension(80, 30));
		btnService.setPreferredSize(new Dimension(80, 30));
		btnService.setMaximumSize(new Dimension(80, 30));
		GridBagConstraints gbc_btnService = new GridBagConstraints();
		gbc_btnService.insets = new Insets(0, 0, 0, 10);

		gbc_btnService.fill = GridBagConstraints.HORIZONTAL;
		gbc_btnService.gridx = 0;
		gbc_btnService.gridy = 4;
		JPanel panel_control = (JPanel) splitPane.getRightComponent();
		panel_control.add(btnService, gbc_btnService);
		btnService.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent e) {
				if (sim.toggleService()) {
					setEventLabel("Service-Mode!", Color.ORANGE);
				} else {
					setEventLabel("", Color.WHITE);
				}
			}
		});
	}
}