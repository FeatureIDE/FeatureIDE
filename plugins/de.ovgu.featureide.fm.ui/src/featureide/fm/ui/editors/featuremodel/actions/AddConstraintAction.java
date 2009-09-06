/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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

import java.util.Iterator;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.prop4j.Node;
import org.prop4j.NodeWriter;

import featureide.fm.core.Constraint;
import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.core.io.UnsupportedModelException;
import featureide.fm.core.io.guidsl.FeatureModelReader;
import featureide.fm.core.io.guidsl.FeatureModelWriter;
import featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;

/**
 *  Add propositional constraint and edit existing constraints
 * 
 * @author Christian Becker
 */
public class AddConstraintAction extends Action {

	private GraphicalViewerImpl viewer;

	protected FeatureModel featuremodel;

	private Shell shell;

	private Button ok;

	private Button cancel;

	private Button add;

	private Button implies;

	private Combo features;

	private Text constraintText;

	private Label errorMessage;

	private Label errorMarker;

	private FeatureModelWriter writer;

	protected String featuretext;

	private Image errorImage;

	private Constraint oldConstraint;

	public AddConstraintAction(GraphicalViewerImpl viewer,
			FeatureModel featuremodel) {
		super("Add propositional constraint");
		this.viewer = viewer;
		this.featuremodel = featuremodel;
	}

	@SuppressWarnings("unchecked")
	public void run() {
		writer = new FeatureModelWriter(featuremodel);
		featuretext = writer.writeToString();
		createEditor();

		oldConstraint = null;
		IStructuredSelection selection = (IStructuredSelection) viewer
				.getSelection();
		Iterator iter = selection.iterator();
		while (iter.hasNext()) {
			Object editPart = iter.next();
			if (editPart instanceof ConstraintEditPart) {
				oldConstraint = ((ConstraintEditPart) editPart)
						.getConstraintModel();
				constraintText.setText(oldConstraint.getNode().toString(
						NodeWriter.textualSymbols));
			}
		}
	}

	private void createEditor() {
		shell = new Shell(viewer.getControl().getDisplay());
		if (oldConstraint == null) {
			shell.setText("Add propositional constraint");
		} else {
			shell.setText("Edit propositional constraint");
		}
		shell.setSize(400, 180);
		GridLayout layout = new GridLayout();
		layout.numColumns = 3;
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

		gridData.horizontalSpan = 2;
		errorMessage.setLayoutData(gridData);

		features = new Combo(shell, SWT.READ_ONLY);
		features.setText("Features");

		for (Feature ft : featuremodel.getFeatures()) {
			features.add(ft.getName());
		}
		features.select(0);

		gridData = new GridData(GridData.FILL_HORIZONTAL);
		features.setLayoutData(gridData);

		add = new Button(shell, SWT.NONE);
		add.setText("Add feature");
		add.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {

				constraintText.append(features.getItem(features
						.getSelectionIndex())
						+ " ");
			}
		});
		gridData = new GridData();
		add.setLayoutData(gridData);

		implies = new Button(shell, SWT.NONE);
		implies.setText("Implies");
		implies
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {
						constraintText.append("implies ");
					}
				});
		gridData = new GridData();
		implies.setLayoutData(gridData);

		constraintText = new Text(shell, SWT.SINGLE | SWT.BORDER);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.horizontalSpan = 3;
		constraintText.setLayoutData(gridData);
		new Label(shell, SWT.NONE);
		ok = new Button(shell, SWT.NONE);
		ok.setText("Ok");
		ok.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {

				String input = constraintText.getText().trim();
				if (input.length() != 0) {

					// Check if the constraint ends with a ';' and add a ';'
					// when not.
					if (!input.endsWith(";")) {
						StringBuffer temp = new StringBuffer(input);
						temp.append(";");
						input = temp.toString();
					}
					try {
						Node propNode = new FeatureModelReader(
								new FeatureModel()).readPropositionalString(
								input, featuremodel);
						featuremodel.addPropositionalNode(propNode);
						featuremodel.handleModelDataChanged();
						if (oldConstraint != null) {
							featuremodel.removePropositionalNode(oldConstraint);
							oldConstraint = null;
						}
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
		ok.setLayoutData(gridData);

		cancel = new Button(shell, SWT.NONE);
		cancel.setText("Abort");
		cancel
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {

						shell.dispose();
					}
				});
		gridData = new GridData(GridData.HORIZONTAL_ALIGN_END);
		gridData.widthHint = 70;
		cancel.setLayoutData(gridData);

		shell.open();

	}

}
