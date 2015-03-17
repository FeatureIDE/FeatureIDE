/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.actions.generator;

import javax.annotation.CheckForNull;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Scale;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * A wizard page for creating T-Wise configurations with SPLCATool.
 * 
 * @author Jens Meinicke
 */
public class BuildProductsPage extends WizardPage implements IConfigurationBuilderBasics {
		
	private static final String LABEL_GENERATE = "&Strategy:";
	private static final String LABEL_ALGORITHM = "&Algorithm:";
	private static final String LABEL_ORDER = "&Order:";
	private static final String LABEL_BUFFER = "&Buffer all configurations:";
	private static final String LABEL_INTERACTIONS = "&Interactions: t=";
	private static final String LABEL_CREATE_NEW_PROJECTS = "&Create new projects:";

	private static final String TOOL_TIP_GENERATE = "Defines the produkt-based strategy.";
	private static final String TOOL_TIP_T_WISE = "Defines the algorithm for t-wise sampling.";
	private static final String TOOL_TIP_ORDER = "Defines how the generated produkts are ordered.";
	private static final String TOOL_TIP_BUFFER = "If enabled, all products are buffered before odering and generation.";
	private static final String TOOL_TIP_T = "Define the t for t-wise generation or interaction-based order.";
	private static final String TOOL_TIP_PROJECT = "Defnies whether the produkts are generated into separate projects or into a folder in this project.";
	
	@CheckForNull
	private IFeatureProject project;

	Text fileName;

	private Combo comboAlgorithm;
	private Button buttonBuildProject;
	private Scale scale;
	private Label labelT;

	private boolean toggleState;

	private int t;

	private String algorithm;

	private Combo comboOrder;

	private Combo comboGenerate;

	private Button buttonBuffer;
	private final String generate;
	private final String order;
	private boolean buffer;

	public BuildProductsPage(String project, IFeatureProject featureProject, String generate,  boolean toggleState, String algorithm, int t, String order, boolean buffer) {
		super(project);
		this.project = featureProject;
		this.toggleState = toggleState;
		this.algorithm = algorithm;
		this.generate = generate;
		this.t = t;
		this.order = order;
		this.buffer = buffer;
		setDescription("Build products for project " + featureProject.getProjectName() + ".");
	}

	@Override
	public void createControl(Composite parent) {
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		Composite composite = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		layout.verticalSpacing = 9;
		composite.setLayout(layout);
		final Label labelGenerate = new Label(composite, SWT.NULL);
		labelGenerate.setText(LABEL_GENERATE);
		labelGenerate.setToolTipText(TOOL_TIP_GENERATE);
		comboGenerate = new Combo(composite, SWT.BORDER | SWT.SINGLE
				| SWT.READ_ONLY);
		comboGenerate.setLayoutData(gd);
		for (BuildType type : BuildType.values()) {
			comboGenerate.add(getBuildTypeText(type));
		}
		comboGenerate.setText(generate);
		
		final Label labelAlgorithm = new Label(composite, SWT.NULL);
		labelAlgorithm.setText(LABEL_ALGORITHM);
		labelAlgorithm.setToolTipText(TOOL_TIP_T_WISE);
		comboAlgorithm = new Combo(composite, SWT.BORDER | SWT.SINGLE
				| SWT.READ_ONLY);
		comboAlgorithm.setLayoutData(gd);
		for (TWise tWise : TWise.values()) {
			comboAlgorithm.add(getTWiseText(tWise));
		}
		comboAlgorithm.setText(algorithm);
		comboAlgorithm.setEnabled(comboGenerate.getText().equals(T_WISE_CONFIGURATIONS));
		
		
		Label labelOrder = new Label(composite, SWT.NULL);
		labelOrder.setText(LABEL_ORDER);
		labelOrder.setToolTipText(TOOL_TIP_ORDER);
		comboOrder = new Combo(composite, SWT.BORDER | SWT.SINGLE
				| SWT.READ_ONLY);
		comboOrder.setLayoutData(gd);
		for (BuildOrder order : BuildOrder.values()) {
			comboOrder.add(getOrderText(order));
		}
		comboOrder.setText(order);
		
		final Label labelBuffer = new Label(composite, SWT.NULL);
		labelBuffer.setText(LABEL_BUFFER);
		labelBuffer.setToolTipText(TOOL_TIP_BUFFER);
		buttonBuffer = new Button(composite, SWT.CHECK);
		buttonBuffer.setLayoutData(gd);
		buttonBuffer.setSelection(buffer);
	
		labelT = new Label(composite, SWT.NULL);
		labelT.setText(LABEL_INTERACTIONS + "10");
		labelT.setToolTipText(TOOL_TIP_T);
		scale = new Scale(composite,SWT.HORIZONTAL);
		scale.setIncrement(1);
		scale.setPageIncrement(1);
		scale.setSelection(t);
		setScale();
		

		final Label labelProject = new Label(composite, SWT.NULL);
		labelProject.setText(LABEL_CREATE_NEW_PROJECTS);
		labelProject.setToolTipText(TOOL_TIP_PROJECT);
		buttonBuildProject = new Button(composite, SWT.CHECK);
		buttonBuildProject.setLayoutData(gd);
		buttonBuildProject.setSelection(toggleState);
		
		setPageComplete(false);
		setControl(composite);
		addListeners();
		dialogChanged();
	}

	private String getOrderText(BuildOrder order) {
		switch (order) {
		case DEFAULT:
			return DEFAULT;
		case DIFFERENCE:
			return DIFFERENCE;
		case INTERACTION:
			return INTERACTIONS;
		default:
			UIPlugin.getDefault().logWarning("Unimplemented switch statement for BuildOrder: " + order);
			break;
		
		}
		return "-Error-";
	}

	private String getTWiseText(TWise tWise) {
		switch (tWise) {
		case CASA:
			return CASA;
		case CHVATAL:
			return CHVATAL;
		case ICPL:
			return ICPL;
		default:
			UIPlugin.getDefault().logWarning("Unimplemented switch statement for TWise: " + tWise);
			break;
		
		}
		return "-Error-";
	}

	String getBuildTypeText(BuildType type) {
		switch (type) {
		case ALL_CURRENT:
			return ALL_CURRENT_CONFIGURATIONS;
		case ALL_VALID:
			return ALL_VALID_CONFIGURATIONS;
		case T_WISE:
			return T_WISE_CONFIGURATIONS;
		default:
			UIPlugin.getDefault().logWarning("Unimplemented switch statement for BuildType: " + type);
			break;
		}
		return "-Error-";
	}

	private void setScale() {
		/** Help content of SPLCATool:
		-t t_wise -a Chvatal -fm <feature_model> -s <strength, 1-4> (-startFrom <covering array>) (-limit <coverage limit>) (-sizelimit <rows>) (-onlyOnes) (-noAllZeros)
		-t t_wise -a ICPL 	 -fm <feature_model> -s <strength, 1-3> (-startFrom <covering array>) (-onlyOnes) (-noAllZeros) [Inexact: (-sizelimit <rows>) (-limit <coverage limit>)] (for 3-wise, -eights <1-8>)
		-t t_wise -a CASA 	 -fm <feature_model> -s <strength, 1-6>
		**/
		
		if (comboOrder.getText().equals(INTERACTIONS) || comboGenerate.getText().equals(T_WISE_CONFIGURATIONS)) {
			scale.setEnabled(true);
		} else {
			scale.setEnabled(false);
		}
		
		String selection = comboAlgorithm.getText();
		int lastSelection = scale.getSelection();
		scale.setMinimum(1);
		if (!comboAlgorithm.isEnabled()) {
			scale.setMaximum(10);
		} else if (selection.equals(CHVATAL)) {
			scale.setMaximum(CHVATAL_MAX);
		} else if (selection.equals(ICPL)) {
			scale.setMaximum(ICPL_MAX);
		} else if (selection.equals(CASA)) {
			scale.setMaximum(CASA_MAX);
		}
		
		if (lastSelection > scale.getMaximum()) {
    		scale.setSelection(scale.getMaximum());
    		labelT.setText(LABEL_INTERACTIONS + scale.getMaximum());
    	}
	}
	
	private void dialogChanged() {
		setPageComplete(false);
		// check
		int perspectiveValue = scale.getSelection();
        labelT.setText(LABEL_INTERACTIONS + perspectiveValue +  "   ");
        
		setPageComplete(true);

	}
	private void addListeners() {
		comboAlgorithm.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				setScale();
			}
		});
		
		scale.addListener(SWT.Selection, new Listener() {
	        public void handleEvent(Event event) {
	        	int selection = scale.getSelection();
        		labelT.setText(LABEL_INTERACTIONS + selection);
	        }
	    });
		
		comboGenerate.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				comboAlgorithm.setEnabled(comboGenerate.getText().equals(T_WISE_CONFIGURATIONS));
				setScale();
				
			}
		});
		
		comboOrder.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				setScale();
			}
		});
		
	}
	
	
	boolean getToggleState() {
		return buttonBuildProject.getSelection();
	}

	String getAlgorithm() {
		String text = comboAlgorithm.getText();
		if (text.contains(" ")) {
			return text.substring(0, text.indexOf(" "));			
		}
		return text;
	}
	
	int getT() {
		return scale.getSelection();
	}
	
	BuildType getGeneration() {
		if (comboGenerate.getText().equals(ALL_CURRENT_CONFIGURATIONS)) {
			return BuildType.ALL_CURRENT;
		}
		if (comboGenerate.getText().equals(ALL_VALID_CONFIGURATIONS)) {
			return BuildType.ALL_VALID;
		}
		if (comboGenerate.getText().equals(T_WISE_CONFIGURATIONS)) {
			return BuildType.T_WISE;
		}
		return null;
	}

	public BuildOrder getOrder() {
		if (comboOrder.getText().equals(DEFAULT)) {
			return BuildOrder.DEFAULT;
		}
		if (comboOrder.getText().equals(DIFFERENCE)) {
			return BuildOrder.DIFFERENCE;
		}
		if (comboOrder.getText().equals(INTERACTIONS)) {
			return BuildOrder.INTERACTION;
		}
		return null;
	}
	
	String getSelectedOrder() {
		return comboOrder.getText();
	}

	public boolean getBuffer() {
		return buttonBuffer.getSelection();
		
	}
}
