/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.program.Program;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.prop4j.Node;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.guidsl.FeatureModelReader;


/**
 * A simple editor for propositional constraints written below the feature
 * diagram.
 * 
 * @author Christian Becker
 * @author Thomas Thuem
 */
public class ConstraintEditor {
	
	public ConstraintEditor(final FeatureModel featuremodel, final Constraint constraint) {
		String displayText = constraint == null ? "Create" : "Edit";
		displayText += " Propositional Constraint";
		String initialValue = constraint == null ? "" : constraint.getNode().toString(
				NodeWriter.textualSymbols);
		
		final Shell shell = new Shell(Display.getCurrent());
		shell.setText(displayText);
		shell.setSize(400, 180);
		GridLayout layout = new GridLayout();
		layout.numColumns = 4;
		shell.setLayout(layout);

		GridData gridData;
		final Label errorMarker = new Label(shell, SWT.NONE);
		final Image errorImage = shell.getDisplay().getSystemImage(SWT.ICON_ERROR);
		gridData = new GridData();

		gridData.widthHint = 32;
		gridData.heightHint = 32;
		errorMarker.setLayoutData(gridData);

		final Label errorMessage = new Label(shell, SWT.SINGLE);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;

		gridData.horizontalSpan = 3;
		errorMessage.setLayoutData(gridData);

		final Combo features = new Combo(shell, SWT.READ_ONLY);
		features.setText("Features");

		for (Feature ft : featuremodel.getFeatures())
			features.add(ft.getName());
		features.select(0);

		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.horizontalSpan = 2;
		features.setLayoutData(gridData);

		Button addButton = new Button(shell, SWT.NONE);
		addButton.setText("Add Feature");
		gridData = new GridData();
		addButton.setLayoutData(gridData);

		Button impliesButton = new Button(shell, SWT.NONE);
		impliesButton.setText("Implies");
		gridData = new GridData();
		impliesButton.setLayoutData(gridData);

		final Text constraintText = new Text(shell, SWT.SINGLE | SWT.BORDER);
		constraintText.setText(initialValue);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.horizontalSpan = 4;
		constraintText.setLayoutData(gridData);

		Button helpButton = new Button(shell, SWT.NONE);
		helpButton.setText("Help");
		helpButton
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {
						Program
								.launch("http://www.cs.utexas.edu/~schwartz/ATS/fopdocs/guidsl.html");
					}
				});
		gridData = new GridData(SWT.BEGINNING);
		helpButton.setLayoutData(gridData);

		new Label(shell, SWT.NONE);
		Button okButton = new Button(shell, SWT.NONE);
		okButton.setText("OK");
		gridData = new GridData(GridData.HORIZONTAL_ALIGN_END);
		gridData.widthHint = 70;
		okButton.setLayoutData(gridData);

		Button cancelButton = new Button(shell, SWT.NONE);
		cancelButton.setText("Cancel");
		gridData = new GridData(GridData.HORIZONTAL_ALIGN_END);
		gridData.widthHint = 70;
		cancelButton.setLayoutData(gridData);

		addButton
		.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(
					org.eclipse.swt.events.SelectionEvent e) {
				StringBuffer temp = new StringBuffer(constraintText
						.getText());
				temp.insert(constraintText.getCaretPosition(), features
						.getItem(features.getSelectionIndex())
						+ " ");
				constraintText.setText(temp.toString());
				constraintText.setFocus();
				constraintText.setSelection(constraintText
						.getCharCount());
			}
		});
		impliesButton
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {
						StringBuffer temp = new StringBuffer(constraintText
								.getText());
						temp.insert(constraintText.getCaretPosition(),
								" implies ");
						constraintText.setText(temp.toString());
						constraintText.setFocus();
						constraintText.setSelection(constraintText
								.getCharCount());
					}
				});
		okButton
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {

						String input = constraintText.getText().trim();
						if (input.length() != 0) {

							// Check if the constraint ends with a ';' and
							// add a ';' when not.
							if (!input.endsWith(";")) {
								StringBuffer temp = new StringBuffer(input);
								temp.append(";");
								input = temp.toString();
							}
							try {
								if (constraint != null)
									featuremodel.removePropositionalNode(constraint);
								Node propNode = new FeatureModelReader(
										new FeatureModel())
										.readPropositionalString(input,
												featuremodel);
								featuremodel.addPropositionalNode(propNode);
								featuremodel.handleModelDataChanged();
								shell.dispose();
							} catch (UnsupportedModelException e1) {
								errorMarker.setImage(errorImage);
								errorMessage.setText(e1.getMessage());
							}
						} else {
							errorMarker.setImage(errorImage);
							errorMessage.setText("Enter a constraint");
						}

					}
				});
		cancelButton
		.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(
					org.eclipse.swt.events.SelectionEvent e) {

				shell.dispose();
			}
		});

		shell.open();
	}
	
}
