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

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.ScrollPaneConstants;
import javax.swing.SwingConstants;
import javax.swing.border.EmptyBorder;

import de.ovgu.featureide.examples.elevator.core.controller.ITickListener;
import de.ovgu.featureide.examples.elevator.core.model.Elevator;
import de.ovgu.featureide.examples.elevator.core.model.ElevatorState;

/**
 * 
 * This class implements a panel with background.
 * 
 * @author FeatureIDE Team
 */
public class MainWindow implements ITickListener {
	private JFrame frmElevatorSample;
	private JSplitPane splitPane;
	private JLabel lblEvent;
	private List<FloorComposite> listFloorComposites = new ArrayList<FloorComposite>();

	public MainWindow() {
	}

	public void initialize(int maxFloors) {
		if (frmElevatorSample != null) {
			return;
		}
		frmElevatorSample = new JFrame();
		frmElevatorSample.setTitle("Elevator Sample");
		frmElevatorSample.setBounds(100, 50, 900, 650); // window position and size
		frmElevatorSample.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

		createBaseStructure();
		createPanelControlsContent(maxFloors);
		addBuilding(maxFloors);
		frmElevatorSample.setVisible(true);
	}

	private void createBaseStructure() {
		JPanel contentPane = new JPanel();
		contentPane.setBorder(new EmptyBorder(5, 5, 5, 5));
		contentPane.setLayout(new BorderLayout(0, 0));
		frmElevatorSample.setContentPane(contentPane);

		splitPane = new JSplitPane();
		splitPane.setResizeWeight(0.5);
		contentPane.add(splitPane, BorderLayout.CENTER);
	}

	private void createPanelControlsContent(int maxFloors) {
		JPanel panelControl = new JPanel();
		try {
			panelControl = new JBackgroundPanel(MainWindow.class.getResourceAsStream("/elevator_inside2.png"));
		} catch (IOException e) {
			e.printStackTrace();
		}
		splitPane.setRightComponent(panelControl);

		GridBagLayout gblPanelControl = new GridBagLayout();
		panelControl.setLayout(gblPanelControl);

		lblEvent = new JLabel("");
		lblEvent.setFont(new Font("Tahoma", Font.BOLD, 15));
		lblEvent.setForeground(Color.WHITE);
		lblEvent.setHorizontalAlignment(SwingConstants.CENTER);
		GridBagConstraints gbc = new GridBagConstraints();
		gbc.gridwidth = 4;
		gbc.insets = new Insets(0, 0, 185, 0);
		gbc.fill = GridBagConstraints.HORIZONTAL;
		gbc.gridx = 0;
		gbc.gridy = 0;
		panelControl.add(lblEvent, gbc);
	}

	private void addBuilding(int maxFloors) {
		JPanel panel_building = new JPanel();
		GridBagLayout layout = new GridBagLayout();
		panel_building.setLayout(layout);

		JScrollPane scrollPane = new JScrollPane(panel_building);
		scrollPane.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS);
		scrollPane.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER);
		scrollPane.getVerticalScrollBar().setUnitIncrement(10);

		GridBagConstraints gbc = new GridBagConstraints();
		gbc.insets = new Insets(0, 0, 0, 0);
		gbc.fill = GridBagConstraints.BOTH;
		gbc.gridx = 2;
		gbc.gridy = 0;
		gbc.anchor = GridBagConstraints.SOUTH;

		for (int i = maxFloors; i >= 0; i--) {
			FloorComposite floor = createFloorComposite(i);
			layout.setConstraints(floor, gbc);
			gbc.gridy += 1;

			panel_building.add(floor);
			listFloorComposites.add(0, floor);
		}

		splitPane.setLeftComponent(scrollPane);
	}
	
	private FloorComposite createFloorComposite(int floor) {
		return new FloorComposite(floor == 0, floor);
	}

	public void setEventLabel(String text, Color color) {
		if (lblEvent != null) {
			lblEvent.setText(text);
			lblEvent.setForeground(color);
		}
	}

	public void onTick(Elevator elevator) {
		ElevatorState state = elevator.getCurrentState();
		int currentFloor = elevator.getCurrentFloor();

		switch (state) {
		case MOVING_UP:
			this.listFloorComposites.get(currentFloor - 1).showImageClose();
			break;
		case MOVING_DOWN:
			this.listFloorComposites.get(currentFloor + 1).showImageClose();
			break;
		case FLOORING:
			runFlooringTasks(currentFloor);
			break;
		}
		this.clearPresent();
		this.listFloorComposites.get(currentFloor).showElevatorIsPresent();
	}
	
	private void runFlooringTasks(int currentFloor) {
		this.listFloorComposites.get(currentFloor).showImageOpen();
	}

	private void clearPresent() {
		for (FloorComposite fl : listFloorComposites) {
			fl.showElevatorNotPresent();
		}
	}
}
