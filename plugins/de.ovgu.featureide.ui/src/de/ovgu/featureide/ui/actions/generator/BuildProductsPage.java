/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.ALL_CURRENT_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.ALL_VALID_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.BUILD_PRODUCTS_FOR_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.CASA;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHVATAL;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFAULT;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFINES_HOW_THE_GENERATED_PRODUKTS_ARE_ORDERED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFINES_THE_ALGORITHM_FOR_T_WISE_SAMPLING_;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFINES_THE_PRODUKT_BASED_STRATEGY_;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFINE_THE_T_FOR_T_WISE_SAMPLING_;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFNIES_WHETHER_THE_PRODUKTS_ARE_GENERATED_INTO_SEPARATE_PROJECTS_OR_INTO_A_FOLDER_IN_THIS_PROJECT_;
import static de.ovgu.featureide.fm.core.localization.StringTable.DISSIMILARITY;
import static de.ovgu.featureide.fm.core.localization.StringTable.ERROR_;
import static de.ovgu.featureide.fm.core.localization.StringTable.ICPL;
import static de.ovgu.featureide.fm.core.localization.StringTable.INTERACTIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.INCLING;
import static de.ovgu.featureide.fm.core.localization.StringTable.RANDOM_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.SEARCHES_FOR_TEST_CASED_IN_THE_GENERATED_PRODUCTS_AND_EXECUTES_THEM_;
import static de.ovgu.featureide.fm.core.localization.StringTable.T_WISE_CONFIGURATIONS;

import javax.annotation.CheckForNull;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
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
 * A wizard page sampling.
 * 
 * @author Jens Meinicke
 */
public class BuildProductsPage extends WizardPage implements IConfigurationBuilderBasics {

	private static final String LABEL_GENERATE = "&Strategy:";
	private static final String LABEL_ALGORITHM = "&Algorithm:";
	private static final String LABEL_ORDER = "&Order:";
	private static final String LABEL_TEST = "&Run JUnit tests:";
	private static final String LABEL_INTERACTIONS = "&Interactions: t=";
	private static final String LABEL_CREATE_NEW_PROJECTS = "&Create new projects:";

	private static final String TOOL_TIP_GENERATE = DEFINES_THE_PRODUKT_BASED_STRATEGY_;
	private static final String TOOL_TIP_T_WISE = DEFINES_THE_ALGORITHM_FOR_T_WISE_SAMPLING_;
	private static final String TOOL_TIP_ORDER = DEFINES_HOW_THE_GENERATED_PRODUKTS_ARE_ORDERED_;
	private static final String TOOL_TIP_TEST= SEARCHES_FOR_TEST_CASED_IN_THE_GENERATED_PRODUCTS_AND_EXECUTES_THEM_;
	private static final String TOOL_TIP_T = DEFINE_THE_T_FOR_T_WISE_SAMPLING_;
	private static final String TOOL_TIP_PROJECT = DEFNIES_WHETHER_THE_PRODUKTS_ARE_GENERATED_INTO_SEPARATE_PROJECTS_OR_INTO_A_FOLDER_IN_THIS_PROJECT_;

	@CheckForNull
	private IFeatureProject project;

	Text fileName;

	private Combo comboAlgorithm;
	private Button buttonBuildProject;
	private Scale scale;
	private Label labelT;

	private boolean buildProjects;

	private int t;

	private String algorithm;

	private Combo comboOrder;

	private Combo comboGenerate;

	private Button buttonTest;
	private final String generate;
	private final String order;
	private boolean test;
	private Text textField;
	private Label labelMax;
	private String maxConfs;

	public BuildProductsPage(String project, IFeatureProject featureProject, String generate, boolean buildProjects, String algorithm, int t, String order, boolean test, String maxConfs) {
		super(project);
		this.project = featureProject;
		this.buildProjects = buildProjects;
		this.algorithm = algorithm;
		this.generate = generate;
		this.t = t;
		this.order = order;
		this.test = test;
		if (maxConfs.equals(Integer.MAX_VALUE + "")) {
			maxConfs = "";
		}	
		this.maxConfs = maxConfs;
		setDescription(BUILD_PRODUCTS_FOR_PROJECT + featureProject.getProjectName() + ".");
	}

	@Override
	public void createControl(Composite parent) {
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		Composite composite = new Composite(parent, SWT.NULL);
		
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		layout.verticalSpacing = 5;
		layout.horizontalSpacing = 7;
		composite.setLayout(layout);
		final Label labelGenerate = new Label(composite, SWT.NULL);
		labelGenerate.setText(LABEL_GENERATE);
		labelGenerate.setToolTipText(TOOL_TIP_GENERATE);
		comboGenerate = new Combo(composite, SWT.BORDER | SWT.SINGLE | SWT.READ_ONLY);
		comboGenerate.setLayoutData(gd);
		for (BuildType type : BuildType.values()) {
			if (type == BuildType.INTEGRATION) {
				continue;
			}
			comboGenerate.add(getBuildTypeText(type));
		}
		comboGenerate.setText(generate);

		final Label labelAlgorithm = new Label(composite, SWT.NULL);
		labelAlgorithm.setText(LABEL_ALGORITHM);
		labelAlgorithm.setToolTipText(TOOL_TIP_T_WISE);
		comboAlgorithm = new Combo(composite, SWT.BORDER | SWT.SINGLE | SWT.READ_ONLY);
		comboAlgorithm.setLayoutData(gd);
		for (TWise tWise : TWise.values()) {
			comboAlgorithm.add(getTWiseText(tWise));
		}
		comboAlgorithm.setText(algorithm);
		comboAlgorithm.setEnabled(comboGenerate.getText().equals(T_WISE_CONFIGURATIONS));

		Label labelOrder = new Label(composite, SWT.NULL);
		labelOrder.setText(LABEL_ORDER);
		labelOrder.setToolTipText(TOOL_TIP_ORDER);
		comboOrder = new Combo(composite, SWT.BORDER | SWT.SINGLE | SWT.READ_ONLY);
		comboOrder.setLayoutData(gd);
		for (BuildOrder order : BuildOrder.values()) {
			comboOrder.add(getOrderText(order));
		}
		comboOrder.setText(order);

		labelT = new Label(composite, SWT.NULL);
		labelT.setText(LABEL_INTERACTIONS + "10");
		labelT.setToolTipText(TOOL_TIP_T);
		scale = new Scale(composite, SWT.HORIZONTAL);
		scale.setMaximum(5);
		scale.setIncrement(1);
		scale.setPageIncrement(1);
		scale.setSelection(t);
		setScale();

		labelMax = new Label(composite, SWT.NULL);
		labelMax.setText("Max Configurations:");
		final String maxToolTip = "Set the maximal number of configs to generate, or empty to create all.";
		labelMax.setToolTipText(maxToolTip);
		textField = new Text(composite, SWT.BORDER);
		textField.setToolTipText(maxToolTip);
		final GridData gridData = new GridData();
		gridData.widthHint = 100;
		textField.setLayoutData(gridData);
		textField.setText(maxConfs);
		
		
		final Label labelTest = new Label(composite, SWT.NULL);
		labelTest.setText(LABEL_TEST);
		labelTest.setToolTipText(TOOL_TIP_TEST);
		buttonTest = new Button(composite, SWT.CHECK);
		buttonTest.setLayoutData(gd);
		buttonTest.setSelection(test);

		final Label labelProject = new Label(composite, SWT.NULL);
		labelProject.setText(LABEL_CREATE_NEW_PROJECTS);
		labelProject.setToolTipText(TOOL_TIP_PROJECT);
		buttonBuildProject = new Button(composite, SWT.CHECK);
		buttonBuildProject.setLayoutData(gd);
		buttonBuildProject.setSelection(buildProjects);
		setPageComplete(false);
		setControl(composite);
		addListeners();
		dialogChanged();
		
		buttonTest.setEnabled(!buttonBuildProject.getSelection());
	}

	private String getOrderText(BuildOrder order) {
		switch (order) {
		case DEFAULT:
			return DEFAULT;
		case DISSIMILARITY:
			return DISSIMILARITY;
		case INTERACTION:
			return INTERACTIONS;
		default:
			UIPlugin.getDefault().logWarning("Unimplemented switch statement for BuildOrder: " + order);
			break;

		}
		return ERROR_;
	}

	private String getTWiseText(TWise tWise) {
		switch (tWise) {
		case CASA:
			return CASA;
		case CHVATAL:
			return CHVATAL;
		case ICPL:
			return ICPL;
		case INCLING: 
			return INCLING;
		default:
			UIPlugin.getDefault().logWarning("Unimplemented switch statement for TWise: " + tWise);
			break;

		}
		return ERROR_;
	}

	String getBuildTypeText(BuildType type) {
		switch (type) {
		case ALL_CURRENT:
			return ALL_CURRENT_CONFIGURATIONS;
		case ALL_VALID:
			return ALL_VALID_CONFIGURATIONS;
		case T_WISE:
			return T_WISE_CONFIGURATIONS;
		case RANDOM:
			return RANDOM_CONFIGURATIONS;
		default:
			UIPlugin.getDefault().logWarning("Unimplemented switch statement for BuildType: " + type);
			break;
		}
		return ERROR_;
	}

	private void setScale() {
		/** Help content of SPLCATool:
		-t t_wise -a Chvatal -fm <feature_model> -s <strength, 1-4> (-startFrom <covering array>) (-limit <coverage limit>) (-sizelimit <rows>) (-onlyOnes) (-noAllZeros)
		-t t_wise -a ICPL 	 -fm <feature_model> -s <strength, 1-3> (-startFrom <covering array>) (-onlyOnes) (-noAllZeros) [Inexact: (-sizelimit <rows>) (-limit <coverage limit>)] (for 3-wise, -eights <1-8>)
		-t t_wise -a CASA 	 -fm <feature_model> -s <strength, 1-6>
		 **/
		int lastSelection = scale.getSelection();
		scale.setMinimum(1);
		if (comboGenerate.getText().equals(T_WISE_CONFIGURATIONS)) {
			scale.setEnabled(true);
			String selection = comboAlgorithm.getText();
			if (!comboAlgorithm.isEnabled()) {
				scale.setMaximum(3);
			} else if (selection.equals(CHVATAL)) {
				scale.setMaximum(CHVATAL_MAX);
			} else if (selection.equals(ICPL)) {
				scale.setMaximum(ICPL_MAX);
			} else if (selection.equals(CASA)) {
				scale.setMaximum(CASA_MAX);
			} else if (selection.equals(INCLING)) {
				scale.setMaximum(MASK_MAX);
				scale.setMinimum(MASK_MAX);
				scale.setSelection(MASK_MAX);
				scale.setEnabled(false);
				labelT.setText(LABEL_INTERACTIONS + "2");
			}
		} else if (comboOrder.getText().equals(INTERACTIONS)) {
			scale.setEnabled(true);
			scale.setMaximum(5);
		} else {
			scale.setEnabled(false);
		}
			
		if (lastSelection > scale.getMaximum()) {
			scale.setSelection(scale.getMaximum());
			labelT.setText(LABEL_INTERACTIONS + scale.getMaximum());
		}
	}

	private void dialogChanged() {
		setPageComplete(false);
		int perspectiveValue = scale.getSelection();
		labelT.setText(LABEL_INTERACTIONS + perspectiveValue + "   ");

		if (!checkMaxConfigurationsEntry()) {
			return;
		}
		setErrorMessage(null);
		setPageComplete(true);
	}

	private boolean checkMaxConfigurationsEntry() {
		try {
			if (textField.getText().isEmpty()) {
				return true;
			}
			int value = Integer.parseInt(textField.getText());
			if (value == 0) {
				setErrorMessage("Number of configurations must be larger than 0 or empty to create all configuraitons.");
				return false;
			}
		} catch (NumberFormatException e) {
			long longValue = 0;
			try {
				longValue = Long.parseLong(textField.getText());
			} catch (NumberFormatException e2) {
				setErrorMessage("NumberFormatException: " + e.getMessage());
				return false;	
			}
			setErrorMessage("Number of configurations " + longValue + " is too large.");
			return false;
		}
		return true;
	}

	private void addListeners() {
		comboAlgorithm.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				setScale();
				dialogChanged();
			}
		});

		scale.addListener(SWT.Selection, new Listener() {
			public void handleEvent(Event event) {
				int selection = scale.getSelection();
				labelT.setText(LABEL_INTERACTIONS + selection);
				dialogChanged();
			}
		});

		comboGenerate.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				final String text = comboGenerate.getText();
				final boolean tWise = text.equals(T_WISE_CONFIGURATIONS);
				comboAlgorithm.setEnabled(tWise);
				setScale();
				dialogChanged();

			}
		});

		comboOrder.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				setScale();
				dialogChanged();
			}
		});
		
		buttonBuildProject.addSelectionListener(new SelectionListener() {
			
			@Override
			public void widgetSelected(SelectionEvent e) {
				buttonTest.setEnabled(!buttonBuildProject.getSelection());
				dialogChanged();
			}
			
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
				// nothing here
			}
		});
		
		textField.addModifyListener(new ModifyListener() {
			@Override
			public void modifyText(ModifyEvent e) {
				dialogChanged();
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
		if (comboGenerate.getText().equals(RANDOM_CONFIGURATIONS)) {
			return BuildType.RANDOM;
		}
		return null;
	}

	public BuildOrder getOrder() {
		if (comboOrder.getText().equals(DISSIMILARITY)) {
			return BuildOrder.DISSIMILARITY;
		}
		if (comboOrder.getText().equals(INTERACTIONS)) {
			return BuildOrder.INTERACTION;
		}
		return BuildOrder.DEFAULT;
	}

	String getSelectedOrder() {
		return comboOrder.getText();
	}
	
	public boolean getTest() {
		return buttonTest.getSelection();
	}
	
	public int getMax() {
		try {
			if (textField.getText().isEmpty()) {
				return Integer.MAX_VALUE;
			}
			return Math.max(0, Integer.parseInt(textField.getText()));
		} catch (NumberFormatException e) {
			return 0;
		}
	}
	
}
