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
package featureide.fm.ui.editors.featuremodel.actions;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.program.Program;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.prop4j.Node;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.core.io.UnsupportedModelException;
import featureide.fm.core.io.guidsl.FeatureModelReader;
import featureide.fm.core.io.guidsl.FeatureModelWriter;

/**
 *  Basic Implementation for the ConstraintEditor. 
 * 
 * @author Christian Becker
 */
public abstract class AbstractConstraintEditorAction extends Action {

	protected GraphicalViewerImpl viewer;
	protected FeatureModel featuremodel;
	private Shell shell;
	private Label errorMarker;
	private Image errorImage;
	private Label errorMessage;
	private Combo features;
	private Button addButton;
	protected Text constraintText;
	private Button impliesButton;
	private Button helpButton;
	private Button okButton;
	private Button cancelButton;
	protected FeatureModelWriter writer;
	protected String featuretext;

	public AbstractConstraintEditorAction(GraphicalViewerImpl viewer,
			FeatureModel featuremodel, String menuname) {
		super(menuname);
		this.viewer = viewer;
		this.featuremodel = featuremodel;
		setEnabled(false);
		viewer.addSelectionChangedListener(listener);

	}

	public abstract void run();

	protected void createEditor(String displayText) {
		shell = new Shell(viewer.getControl().getDisplay());
		shell.setText(displayText);
		shell.setSize(400, 180);
		GridLayout layout = new GridLayout();
		layout.numColumns = 4;
		shell.setLayout(layout);

		GridData gridData;
		errorMarker = new Label(shell, SWT.NONE);
		errorImage = shell.getDisplay().getSystemImage(SWT.ICON_ERROR);
		gridData = new GridData();

		gridData.widthHint = 32;
		gridData.heightHint = 32;
		errorMarker.setLayoutData(gridData);

		errorMessage = new Label(shell, SWT.SINGLE);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;

		gridData.horizontalSpan = 3;
		errorMessage.setLayoutData(gridData);

		features = new Combo(shell, SWT.READ_ONLY);
		features.setText("Features");

		for (Feature ft : featuremodel.getFeatures()) {
			features.add(ft.getName());
		}
		features.select(0);

		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.horizontalSpan = 2;
		features.setLayoutData(gridData);

		addButton = new Button(shell, SWT.NONE);
		addButton.setText("Add Feature");
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
		gridData = new GridData();
		addButton.setLayoutData(gridData);

		impliesButton = new Button(shell, SWT.NONE);
		impliesButton.setText("Implies");
		impliesButton
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(	org.eclipse.swt.events.SelectionEvent e) {
						StringBuffer temp = new StringBuffer(constraintText
								.getText());
						temp.insert(constraintText.getCaretPosition(),
								" implies ");
						constraintText.setText(temp.toString());
						constraintText.setFocus();
						constraintText.setSelection(constraintText
								.getCharCount());
						// constraintText.append("implies ");
					}
				});
		gridData = new GridData();
		impliesButton.setLayoutData(gridData);

		constraintText = new Text(shell, SWT.SINGLE | SWT.BORDER);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.horizontalSpan = 4;
		constraintText.setLayoutData(gridData);

		helpButton = new Button(shell, SWT.NONE);
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
		okButton = new Button(shell, SWT.NONE);
		okButton.setText("OK");
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
								Node propNode = new FeatureModelReader(
										new FeatureModel())
										.readPropositionalString(input,
												featuremodel);
								featuremodel.addPropositionalNode(propNode);
								featuremodel.handleModelDataChanged();
								editorhook();
								featuremodel.handleModelDataChanged();
								shell.dispose();
								// System.out.println(propNode.toString(NodeWriter.textualSymbols));
							} catch (UnsupportedModelException e1) {
								errorMarker.setImage(errorImage);
								errorMessage.setText(e1.getMessage());
							}
						} else {
							errorMarker.setImage(errorImage);
							errorMessage.setText("Enter a constraint");
							// errorMarker.setImage(errorImage);
						}

					}
				});
		gridData = new GridData(GridData.HORIZONTAL_ALIGN_END);
		gridData.widthHint = 70;
		okButton.setLayoutData(gridData);

		cancelButton = new Button(shell, SWT.NONE);
		cancelButton.setText("Cancel");
		cancelButton
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {

						shell.dispose();
					}
				});
		gridData = new GridData(GridData.HORIZONTAL_ALIGN_END);
		gridData.widthHint = 70;
		cancelButton.setLayoutData(gridData);

		shell.open();
	}

	
	protected void editorhook() {

	}

	protected abstract boolean isValidSelection(IStructuredSelection selection);

	private ISelectionChangedListener listener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection selection = (IStructuredSelection) event
					.getSelection();
			setEnabled(isValidSelection(selection));
		}
	};

}
