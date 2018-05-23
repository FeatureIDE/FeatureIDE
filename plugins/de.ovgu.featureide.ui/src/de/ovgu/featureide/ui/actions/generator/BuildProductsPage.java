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
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFNIES_WHETHER_THE_PRODUKTS_ARE_GENERATED_INTO_SEPARATE_PROJECTS_OR_INTO_A_FOLDER_IN_THIS_PROJECT_;
import static de.ovgu.featureide.fm.core.localization.StringTable.DISSIMILARITY;
import static de.ovgu.featureide.fm.core.localization.StringTable.ERROR_;
import static de.ovgu.featureide.fm.core.localization.StringTable.ICPL;
import static de.ovgu.featureide.fm.core.localization.StringTable.INCLING;
import static de.ovgu.featureide.fm.core.localization.StringTable.INTERACTIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.RANDOM_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.SEARCHES_FOR_TEST_CASED_IN_THE_GENERATED_PRODUCTS_AND_EXECUTES_THEM_;
import static de.ovgu.featureide.fm.core.localization.StringTable.T_WISE_CONFIGURATIONS;

import java.util.ArrayList;

import javax.annotation.CheckForNull;

import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.ScrolledComposite;
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
import org.eclipse.swt.widgets.Group;
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

	private static final String JUNIT_PLUGIN_WARNING = "Testing generated producted requires plugin \"org.junit\" which cannot be found.";
	private static final String LABEL_GENERATE = "&Strategy:";
	private static final String LABEL_ALGORITHM = "&Algorithm:";
	private static final String LABEL_ORDER = "&Order:";
	private static final String LABEL_TEST = "&Run JUnit tests:";
	private static final String LABEL_INTERACTIONS = "&Interactions: T=";
	private static final String LABEL_CREATE_NEW_PROJECTS = "&Create new projects:";

	private static final String TOOL_TIP_GENERATE = DEFINES_THE_PRODUKT_BASED_STRATEGY_;
	private static final String TOOL_TIP_T_WISE = DEFINES_THE_ALGORITHM_FOR_T_WISE_SAMPLING_;
	private static final String TOOL_TIP_ORDER = DEFINES_HOW_THE_GENERATED_PRODUKTS_ARE_ORDERED_;
	private static final String TOOL_TIP_TEST = SEARCHES_FOR_TEST_CASED_IN_THE_GENERATED_PRODUCTS_AND_EXECUTES_THEM_;
	private static final String TOOL_TIP_T = "Define the T for T-wise sampling.";
	private static final String TOOL_TIP_T_ORDER = "Define the T for odering by interactions.";
	private static final String TOOL_TIP_PROJECT = DEFNIES_WHETHER_THE_PRODUKTS_ARE_GENERATED_INTO_SEPARATE_PROJECTS_OR_INTO_A_FOLDER_IN_THIS_PROJECT_;

	private static boolean JUNIT_INSTALLED = Platform.getBundle("org.junit") != null;

	@CheckForNull
	private final IFeatureProject project;

	Text fileName;

	private Combo comboAlgorithm;
	private Button buttonBuildProject;
	private Scale scaleTWise;
	private Scale scaleInteraction;
	private Label labelTWise;
	private Label labelOrderInteraction;

	private final boolean buildProjects;

	private final int t;
	private final int t_Interaction;

	private final String algorithm;

	private Combo comboOrder;

	private Combo comboGenerate;

	private Button buttonTest;
	private final String generate;
	private final String order;
	private final boolean test;
	private Text textField;
	private Label labelMax;
	private final String maxConfs;

	public BuildProductsPage(String project, IFeatureProject featureProject, String generate, boolean buildProjects, String algorithm, int t, int t_Interaction,
			String order, boolean test, String maxConfs) {
		super(project);
		this.project = featureProject;
		this.buildProjects = buildProjects;
		this.algorithm = algorithm;
		this.generate = generate;
		this.t = t;
		this.t_Interaction = t_Interaction;
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
		final ArrayList<Label> labels = new ArrayList<Label>();

		final ScrolledComposite scrlcomp = new ScrolledComposite(parent, SWT.V_SCROLL);
		final Composite container = new Composite(scrlcomp, SWT.NONE);
		scrlcomp.setExpandHorizontal(true);
		scrlcomp.setContent(container);

		final GridLayout layout = new GridLayout();
		layout.numColumns = 1;
		layout.marginBottom = 10;
		container.setLayout(layout);
		final GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.horizontalSpan = 1;
		container.setLayoutData(gridData);

		final GridData gd_Fill_H = new GridData(GridData.FILL_HORIZONTAL);
		final GridData gd_LeftColumnInsideGroup = new GridData();
		final GridData gd_LeftColumn = new GridData();

		final Group groupDeriveConf = new Group(container, SWT.SHADOW_ETCHED_IN);
		groupDeriveConf.setText("Derive configurations");
		GridLayout groupLayout = new GridLayout();
		groupLayout.numColumns = 2;
		groupLayout.verticalSpacing = 5;
		groupDeriveConf.setLayout(groupLayout);
		GridData gridDataGroup = new GridData();
		gridDataGroup.grabExcessHorizontalSpace = true;
		gridDataGroup.horizontalAlignment = GridData.FILL;
		groupDeriveConf.setLayoutData(gridDataGroup);

		final Label labelGenerate = new Label(groupDeriveConf, SWT.NULL);
		labelGenerate.setText(LABEL_GENERATE);
		labelGenerate.setToolTipText(TOOL_TIP_GENERATE);
		labelGenerate.setLayoutData(gd_LeftColumnInsideGroup);
		labels.add(labelGenerate);
		comboGenerate = new Combo(groupDeriveConf, SWT.BORDER | SWT.SINGLE | SWT.READ_ONLY);
		comboGenerate.setLayoutData(gd_Fill_H);
		for (final BuildType type : BuildType.values()) {
			if (type == BuildType.INTEGRATION) {
				continue;
			}
			comboGenerate.add(getBuildTypeText(type));
		}
		comboGenerate.setText(generate);

		final Label labelAlgorithm = new Label(groupDeriveConf, SWT.NULL);
		labelAlgorithm.setText(LABEL_ALGORITHM);
		labelAlgorithm.setToolTipText(TOOL_TIP_T_WISE);
		labelAlgorithm.setLayoutData(gd_LeftColumnInsideGroup);
		labels.add(labelAlgorithm);
		comboAlgorithm = new Combo(groupDeriveConf, SWT.BORDER | SWT.SINGLE | SWT.READ_ONLY);
		comboAlgorithm.setLayoutData(gd_Fill_H);

		for (final TWise tWise : TWise.values()) {
			final String tWiseText = getTWiseText(tWise);
			if (tWiseText != null) {
				comboAlgorithm.add(tWiseText);
			}
		}
		comboAlgorithm.setText(algorithm);
		comboAlgorithm.setEnabled(comboGenerate.getText().equals(T_WISE_CONFIGURATIONS));

		labelTWise = new Label(groupDeriveConf, SWT.NULL);
		labelTWise.setText(LABEL_INTERACTIONS + "10");
		labelTWise.setToolTipText(TOOL_TIP_T);
		labelTWise.setLayoutData(gd_LeftColumnInsideGroup);
		labels.add(labelTWise);
		scaleTWise = new Scale(groupDeriveConf, SWT.HORIZONTAL);
		scaleTWise.setLayoutData(gd_Fill_H);
		scaleTWise.setMaximum(5);
		scaleTWise.setIncrement(1);
		scaleTWise.setPageIncrement(1);
		scaleTWise.setSelection(t);
		setScaleTWise();

		labelMax = new Label(groupDeriveConf, SWT.NULL);
		labelMax.setText("Max Configurations:");
		final String maxToolTip = "Set the maximal number of configs to generate, or empty to create all.";
		labelMax.setToolTipText(maxToolTip);
		labelMax.setLayoutData(gd_LeftColumnInsideGroup);
		labels.add(labelMax);
		textField = new Text(groupDeriveConf, SWT.BORDER);
		textField.setToolTipText(maxToolTip);
		final GridData gridDataWidth = new GridData();
		gridDataWidth.widthHint = 100;
		textField.setLayoutData(gridDataWidth);
		textField.setText(maxConfs);

		final Group groupOrder = new Group(container, SWT.SHADOW_ETCHED_IN);
		groupOrder.setText("Order configurations");
		groupLayout = new GridLayout();
		groupLayout.numColumns = 2;
		groupLayout.verticalSpacing = 5;
		groupOrder.setLayout(groupLayout);
		gridDataGroup = new GridData();
		gridDataGroup.grabExcessHorizontalSpace = true;
		gridDataGroup.horizontalAlignment = GridData.FILL;
		groupOrder.setLayoutData(gridDataGroup);

		final Label labelOrder = new Label(groupOrder, SWT.NULL);
		labelOrder.setText(LABEL_ORDER);
		labelOrder.setToolTipText(TOOL_TIP_ORDER);
		labelOrder.setLayoutData(gd_LeftColumnInsideGroup);
		labels.add(labelOrder);
		comboOrder = new Combo(groupOrder, SWT.BORDER | SWT.SINGLE | SWT.READ_ONLY);
		comboOrder.setLayoutData(gd_Fill_H);
		for (final BuildOrder order : BuildOrder.values()) {
			comboOrder.add(getOrderText(order));
		}
		comboOrder.setText(order);

		labelOrderInteraction = new Label(groupOrder, SWT.NULL);
		labelOrderInteraction.setText(LABEL_INTERACTIONS + "1");
		labelOrderInteraction.setToolTipText(TOOL_TIP_T_ORDER);
		labelOrderInteraction.setLayoutData(gd_LeftColumnInsideGroup);
		labels.add(labelOrderInteraction);
		scaleInteraction = new Scale(groupOrder, SWT.HORIZONTAL);
		scaleInteraction.setLayoutData(gd_Fill_H);
		scaleInteraction.setMaximum(5);
		scaleInteraction.setIncrement(1);
		scaleInteraction.setPageIncrement(1);
		scaleInteraction.setSelection(t_Interaction);
		setScaleInteraction();

		final Composite jUnitContainer = new Composite(container, SWT.NONE);
		final Label labelProject = new Label(jUnitContainer, SWT.NULL);
		labelProject.setText(LABEL_CREATE_NEW_PROJECTS);
		labelProject.setToolTipText(TOOL_TIP_PROJECT);
		labels.add(labelProject);
		buttonBuildProject = new Button(jUnitContainer, SWT.CHECK);
		buttonBuildProject.setLayoutData(gd_Fill_H);
		buttonBuildProject.setSelection(buildProjects);

		groupLayout = new GridLayout();
		groupLayout.numColumns = 2;
		groupLayout.verticalSpacing = 5;
		jUnitContainer.setLayout(groupLayout);
		gridDataGroup = new GridData();
		gridDataGroup.grabExcessHorizontalSpace = true;
		gridDataGroup.horizontalAlignment = GridData.FILL;
		jUnitContainer.setLayoutData(gridDataGroup);

		final Label labelTest = new Label(jUnitContainer, SWT.NULL);
		labelTest.setText(LABEL_TEST);
		labelTest.setToolTipText(TOOL_TIP_TEST);
		labelTest.setLayoutData(gd_LeftColumn);
		labels.add(labelTest);
		buttonTest = new Button(jUnitContainer, SWT.CHECK);
		buttonTest.setLayoutData(gridDataGroup);
		buttonTest.setSelection(test);

		container.setSize(container.computeSize(SWT.DEFAULT, SWT.DEFAULT));

		int widthOfLabel = 0;
		for (final Label label : labels) {
			if (label.getSize().x > widthOfLabel) {
				widthOfLabel = label.getSize().x;
			}
		}
		gd_LeftColumnInsideGroup.widthHint = widthOfLabel;
		gd_LeftColumn.widthHint = gd_LeftColumnInsideGroup.widthHint + 3;

		setControl(scrlcomp);
		setPageComplete(false);
		addListeners();
		dialogChanged();

		buttonTest.setEnabled(!buttonBuildProject.getSelection());

		if (!JUNIT_INSTALLED) {
			buttonTest.setSelection(false);
			buttonTest.setEnabled(false);
			buttonTest.setToolTipText(JUNIT_PLUGIN_WARNING);
			labelTest.setToolTipText(JUNIT_PLUGIN_WARNING);
		}
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
			final boolean windowsOS = System.getProperty("os.name").startsWith("Windows");
			return windowsOS ? CASA : null;
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

	private void setScaleInteraction() {
		final int lastSelection = scaleInteraction.getSelection();
		scaleInteraction.setMinimum(1);
		if (comboOrder.getText().equals(INTERACTIONS)) {
			scaleInteraction.setEnabled(true);
			scaleInteraction.setMaximum(5);
		} else {
			scaleInteraction.setEnabled(false);
		}

		if (lastSelection > scaleInteraction.getMaximum()) {
			scaleInteraction.setSelection(scaleInteraction.getMaximum());
			labelOrderInteraction.setText(LABEL_INTERACTIONS + scaleInteraction.getMaximum());
		}
	}

	private void setScaleTWise() {
		/**
		 * Help content of SPLCATool: -t t_wise -a Chvatal -fm <feature_model> -s <strength, 1-4> (-startFrom <covering array>) (-limit <coverage limit>)
		 * (-sizelimit <rows>) (-onlyOnes) (-noAllZeros) -t t_wise -a ICPL -fm <feature_model> -s <strength, 1-3> (-startFrom <covering array>) (-onlyOnes)
		 * (-noAllZeros) [Inexact: (-sizelimit <rows>) (-limit <coverage limit>)] (for 3-wise, -eights <1-8>) -t t_wise -a CASA -fm <feature_model> -s
		 * <strength, 1-6>
		 **/
		final int lastSelection = scaleTWise.getSelection();
		scaleTWise.setMinimum(1);
		if (comboGenerate.getText().equals(T_WISE_CONFIGURATIONS)) {
			scaleTWise.setEnabled(true);
			final String selection = comboAlgorithm.getText();
			if (!comboAlgorithm.isEnabled()) {
				scaleTWise.setMaximum(3);
			} else if (selection.equals(CHVATAL)) {
				scaleTWise.setMaximum(CHVATAL_MAX);
			} else if (selection.equals(ICPL)) {
				scaleTWise.setMaximum(ICPL_MAX);
			} else if (selection.equals(CASA)) {
				scaleTWise.setMaximum(CASA_MAX);
			} else if (selection.equals(INCLING)) {
				scaleTWise.setMaximum(MASK_MAX);
				scaleTWise.setMinimum(MASK_MAX);
				scaleTWise.setSelection(MASK_MAX);
				scaleTWise.setEnabled(false);
				labelTWise.setText(LABEL_INTERACTIONS + "2");
			}
		} else {
			scaleTWise.setEnabled(false);
		}

		if (lastSelection > scaleTWise.getMaximum()) {
			scaleTWise.setSelection(scaleTWise.getMaximum());
			labelTWise.setText(LABEL_INTERACTIONS + scaleTWise.getMaximum());
		}
	}

	private void dialogChanged() {
		setPageComplete(false);
		int perspectiveValue = scaleTWise.getSelection();
		labelTWise.setText(LABEL_INTERACTIONS + perspectiveValue + "   ");
		perspectiveValue = scaleInteraction.getSelection();
		labelOrderInteraction.setText(LABEL_INTERACTIONS + perspectiveValue + "   ");

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
			final int value = Integer.parseInt(textField.getText());
			if (value == 0) {
				setErrorMessage("Number of configurations must be larger than 0 or empty to create all configuraitons.");
				return false;
			}
		} catch (final NumberFormatException e) {
			long longValue = 0;
			try {
				longValue = Long.parseLong(textField.getText());
			} catch (final NumberFormatException e2) {
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

			@Override
			public void modifyText(ModifyEvent e) {
				setScaleTWise();
				dialogChanged();
			}
		});

		scaleTWise.addListener(SWT.Selection, new Listener() {

			@Override
			public void handleEvent(Event event) {
				final int selection = scaleTWise.getSelection();
				labelTWise.setText(LABEL_INTERACTIONS + selection);
				dialogChanged();
			}
		});

		scaleInteraction.addListener(SWT.Selection, new Listener() {

			@Override
			public void handleEvent(Event event) {
				final int selection = scaleInteraction.getSelection();
				labelOrderInteraction.setText(LABEL_INTERACTIONS + selection);
				dialogChanged();
			}
		});

		comboGenerate.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				final String text = comboGenerate.getText();
				final boolean tWise = text.equals(T_WISE_CONFIGURATIONS);
				comboAlgorithm.setEnabled(tWise);
				setScaleTWise();
				dialogChanged();
			}
		});

		comboOrder.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				setScaleInteraction();
				dialogChanged();
			}
		});

		buttonBuildProject.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				buttonTest.setEnabled(!buttonBuildProject.getSelection());
				if (!JUNIT_INSTALLED) {
					buttonTest.setEnabled(false);
				}
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
		final String text = comboAlgorithm.getText();
		if (text.contains(" ")) {
			return text.substring(0, text.indexOf(" "));
		}
		return text;
	}

	int getT() {
		return scaleTWise.getSelection();
	}

	int getTInteraction() {
		return scaleInteraction.getSelection();
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
		} catch (final NumberFormatException e) {
			return 0;
		}
	}

}
