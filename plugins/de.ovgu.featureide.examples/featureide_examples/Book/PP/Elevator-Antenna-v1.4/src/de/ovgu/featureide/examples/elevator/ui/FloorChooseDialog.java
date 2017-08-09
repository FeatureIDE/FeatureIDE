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
// #if FIFO | FloorPermission
package de.ovgu.featureide.examples.elevator.ui;

import java.awt.Component;
import java.awt.FlowLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.List;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JToggleButton;
import javax.swing.SwingConstants;

public class FloorChooseDialog extends JDialog {

	private static final long serialVersionUID = 5663011468166401169L;
	private JPanel panelFloors;
	private List<Integer> selectedFloors = new ArrayList<>();
	
	public FloorChooseDialog(int maxFloors, 
			//#if FloorPermission 
			List<Integer> disabledFloors,
			//#endif
			String description) {
		
		setModal(true);
		setTitle("Choose Floor");
		setSize(220, 220);
		setLayout(new FlowLayout());
		
		JPanel panelLevel = new JPanel(new FlowLayout());
		JLabel lblLevel = new JLabel(description);
		lblLevel.setHorizontalTextPosition(SwingConstants.CENTER);
		lblLevel.setHorizontalAlignment(SwingConstants.CENTER);
		panelLevel.add(lblLevel);
		add(panelLevel);
		
		panelFloors = new JPanel(new GridLayout(0,3));
		for (int i = 0; i <= maxFloors; i++) {
			//#if FloorPermission
			if (disabledFloors.contains(i)) {
				continue;
			}
			//#endif
			JToggleButton btnFloor = new JToggleButton(String.valueOf(i));
			btnFloor.setActionCommand(String.valueOf(i));
			btnFloor.addActionListener(new SelectFloorActionListener());
			panelFloors.add(btnFloor);
		}
		add(panelFloors);
		
		JButton submit = new JButton("Submit");
		submit.addActionListener(new SubmitFloorActionListener());
		add(submit);
		
		setVisible(true);
	}

	public List<Integer> getSelectedFloors() {
		return selectedFloors ;
	}

	public class SubmitFloorActionListener implements ActionListener {
		@Override
		public void actionPerformed(ActionEvent e) {
			for (Component component : panelFloors.getComponents()) {
				JToggleButton btn = ((JToggleButton)component);
				if (btn.isSelected())
					selectedFloors.add(Integer.parseInt(btn.getActionCommand()));
			}
			setVisible(false);
		}
	}
	
	private static class SelectFloorActionListener implements ActionListener {
		@Override
		public void actionPerformed(ActionEvent e) {
			JToggleButton button = (JToggleButton) e.getSource();
			button.setEnabled(false);
		}
	}

}
// #endif
