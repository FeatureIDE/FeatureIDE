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
//		gbc_btnService.gridwidth = 4;

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