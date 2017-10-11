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
package de.ovgu.featureide.fm.ui.editors;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADD_ATTRIBUTE;

import java.awt.Container;
import java.awt.Dimension;
import java.awt.Frame;
import java.awt.GridBagLayout;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.GridBagConstraints;
import java.awt.Insets;
import java.awt.Label;
import java.awt.Panel;
import java.awt.TextField;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextField;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.ColumnViewerEditor;
import org.eclipse.jface.viewers.ColumnViewerEditorActivationEvent;
import org.eclipse.jface.viewers.ColumnViewerEditorActivationStrategy;
import org.eclipse.jface.viewers.EditingSupport;
import org.eclipse.jface.viewers.FocusCellOwnerDrawHighlighter;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.jface.viewers.TreePath;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.jface.viewers.TreeViewerEditor;
import org.eclipse.jface.viewers.TreeViewerFocusCellManager;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.core.base.impl.FeatureAttributeInherited;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;

/**
 * A simple editor to change description of a particular feature diagram.
 *
 */
public class AddAttributeDialog extends Dialog {

	private IFeatureModel featureModel;
	private IFeature feature;

	public AddAttributeDialog(final Shell parentShell, IFeatureModel featureModel, IFeature feature) {
		super(parentShell);
		this.featureModel = featureModel;
		this.feature = feature;
	}

	/**
	 * Sets the minimal size and the text in the title of the dialog.
	 *
	 * @param newshell
	 */
	@Override
	protected void configureShell(Shell newShell) {
		super.configureShell(newShell);
		newShell.setText(ADD_ATTRIBUTE);
	}

	@Override
	protected Point getInitialSize() {
		return new Point(350, 400);
	}

	/**
	 * Creates the general layout of the dialog.
	 *
	 * @param parent
	 */
	@Override
	protected Control createDialogArea(Composite parent) {

		final Composite dialog = (Composite) super.createDialogArea(parent);
		dialog.setBackground(new Color(parent.getDisplay(), 255, 255, 255));
//		final GridLayout gbc = new GridLayout();
//		gbc.numColumns = 2;
//		dialog.setLayout(gridLayout);
		
//		dialog.setLayoutData(new GridBagLayout());
//		JLabel jLabel = new JLabel("Selected Feature: " + feature.getName());
//
//		GridBagConstraints gbc = new GridBagConstraints();
//
//		gbc.insets = new Insets(5, 0, 5, 0);
//
//		gbc.gridx = 0;
//		gbc.gridy = 0;
//
//				dialog.add(jLabel, gbc);
//
//		gbc.gridy++;
//
//		Panel jPanel = new Panel();
//		Label jName = new Label("Name: ");
//		jPanel.add(jName);
//		final TextField textFieldName = new TextField(20);
//		jPanel.add(textFieldName, gbc);
//				dialog.add(jPanel, gbc);
//		gbc.gridy++;
//
//		Panel jPanelValue = new Panel();
//		Label jLabelValue = new Label("Value: ");
//		final TextField textFieldValue = new TextField(20);
//		jPanelValue.add(jLabelValue);
//		jPanelValue.add(textFieldValue);
//				dialog.add(jPanelValue, gbc);
//
//		gbc.gridy++;
//
//		Panel jPanelUnit = new Panel();
//		JLabel jLabelUnit = new JLabel("Unit: ");
//		final JTextField textFieldUnit = new JTextField(20);
//		jPanelUnit.add(jLabelUnit);
//		jPanelUnit.add(textFieldUnit);
//				dialog.add(jPanelUnit, gbc);
//		gbc.gridy++;
//
//		String[] Types = { "String", "Long", "Double", "Boolean" };
//		Panel jPanelType = new Panel();
//		Label jLabelType = new Label("Type: ");
//		final Combo typeBox = new Combo(dialog, SWT.READ_ONLY);
//		typeBox.setItems(Types);
//				typeBox.addActionListener(new ActionListener() {
//
//					public void actionPerformed(ActionEvent e) {
//						JComboBox typeBox = (JComboBox) e.getSource();
//						String typeName = (String) typeBox.getSelectedItem();
//					}
//				});
//
//		jPanelType.add(jLabelType);
//				jPanelType.add(typeBox);
//				dialog.add(jPanelType, gbc);
//
//		gbc.gridy++;
//
//		String[] bools = { "true", "false" };
//		Panel jPanelRecursive = new Panel();
//		Label jLabelRecursive = new Label("Recursive: ");
//		final Combo recursiveBox = new Combo(dialog, SWT.READ_ONLY);
//		recursiveBox.setItems(bools);
//				typeBox.addActionListener(new ActionListener() {
//
//					public void actionPerformed(ActionEvent e) {
//						JComboBox<String> typeBox = (JComboBox) e.getSource();
//						String typeName = (String) typeBox.getSelectedItem();
//					}
//				});
//
//		jPanelRecursive.add(jLabelRecursive);
//				jPanelRecursive.add(recursiveBox);
//				dialog.add(jPanelRecursive, gbc);
//
//		gbc.gridy++;
//
//		Panel jPanelConfigurable = new Panel();
//		Label jLabelConfigurable = new Label("Configurable: ");
//		final Combo configurableBox = new Combo(dialog, SWT.READ_ONLY);
//		configurableBox.setItems(bools);
//				typeBox.addActionListener(new ActionListener() {
//
//					public void actionPerformed(ActionEvent e) {
//						JComboBox<String> configurableBox = (JComboBox) e.getSource();
//						String typeName = (String) configurableBox.getSelectedItem();
//					}
//				});
//
//		jPanelConfigurable.add(jLabelConfigurable);
//				jPanelConfigurable.add(configurableBox);
//				dialog.add(jPanelConfigurable, gbc);
//
//		gbc.gridy++;
//
//		Button bCancel = new Button("Cancel");
//		bCancel.addActionListener(new ActionListener() {
//
//			public void actionPerformed(ActionEvent e) {
//				dialog.dispose();
//			}
//		});
//		Button bAdd = new Button("Add");
//		bAdd.addActionListener(new ActionListener() {
//
//			public void actionPerformed(ActionEvent e) {
//				String name = textFieldName.getText().trim();
//				String value = textFieldValue.getText().trim();
				// String type = typeBox.getSelectedItem().toString().trim();
//				String unit = textFieldUnit.getText().trim();
				// String recursive = recursiveBox.getSelectedItem().toString().trim();
				// String configurable = configurableBox.getSelectedItem().toString().trim();
//						boolean rec = false, conf = false;
//						rec = recursive.equals("true");
//						conf = configurable.equals("true");
//
//						FeatureAttribute attribute = new FeatureAttribute(name, value, type, unit, rec, conf);
//						feature.getStructure().getAttributeList().add(attribute);
//				dialog.dispose();
//			}
//		});
//
//		Panel jpButton = new Panel();
//		jpButton.add(bCancel);
//		jpButton.add(bAdd);
//				dialog.add(jpButton, gbc);

		return parent;
	}
}
