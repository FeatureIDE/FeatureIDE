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
package de.ovgu.featureide.fm.ui.preferences;

import java.util.List;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;
import org.prop4j.solver.AbstractSolverFactory;
import org.prop4j.solver.impl.SolverManager;
import org.prop4j.solver.impl.Ltms.LtmsSatSolverFactory;
import org.prop4j.solver.impl.sat4j.Sat4JSatSolverFactory;

import de.ovgu.featureide.fm.core.localization.StringTable;

public class FeatureIDEPreferenceSolverPage extends PreferencePage implements IWorkbenchPreferencePage {

	private final List<AbstractSolverFactory> registeredFactories = SolverManager.getInstance().getExtensions();

	private ComboFieldEditor fASolver;
	private ComboFieldEditor fDSolver;

	public FeatureIDEPreferenceSolverPage() {}

	public FeatureIDEPreferenceSolverPage(String title) {
		super(title);
	}

	public FeatureIDEPreferenceSolverPage(String title, ImageDescriptor image) {
		super(title, image);
	}

	@Override
	public void init(IWorkbench workbench) {
		setPreferenceStore(new ScopedPreferenceStore(InstanceScope.INSTANCE, SolverManager.PREFERENCE_STORE_PATH));
		getPreferenceStore().setDefault(SolverManager.FEATURE_MODEL_ANALYSIS_SOLVER, Sat4JSatSolverFactory.ID);
		getPreferenceStore().setDefault(SolverManager.FEATURE_MODEL_DEFECT_SOLVER, LtmsSatSolverFactory.ID);
	}

	@Override
	protected Control createContents(Composite parent) {
		final Composite container = new Composite(parent, SWT.NULL);
		container.setLayout(new FillLayout(SWT.VERTICAL));
		createFeatureAnalysisSolverSettings(container);
		createFeatureDefectExplanationSolverSettings(container);
		return container;
	}

	private void createFeatureAnalysisSolverSettings(Composite parent) {
		final Group featureModelAnalysisGroup = new Group(parent, SWT.SHADOW_IN);
		featureModelAnalysisGroup.setText(StringTable.CONFIGURATION_FEATUREMODEL_ANALYSIS_SETTINGS);
		featureModelAnalysisGroup.setLayout(new RowLayout(SWT.VERTICAL));
		featureModelAnalysisGroup.setToolTipText(StringTable.CONFIGURATION_FEATUREMODEL_ANALYSIS_SETTINGS_TOOLTIP);
		fASolver = new ComboFieldEditor(SolverManager.FEATURE_MODEL_ANALYSIS_SOLVER, "Solver: ", getSolverNamesAndValues(), featureModelAnalysisGroup);
		fASolver.setPage(this);
		fASolver.setPreferenceStore(getPreferenceStore());
		fASolver.load();
	}

	private void createFeatureDefectExplanationSolverSettings(Composite parent) {
		final Group featureModelAnalysisGroup = new Group(parent, SWT.SHADOW_IN);
		featureModelAnalysisGroup.setText(StringTable.CONFIGURATION_FEATUREMODEL_DEFECT_EXPLANATION_SETTINGS);
		featureModelAnalysisGroup.setLayout(new RowLayout(SWT.VERTICAL));
		featureModelAnalysisGroup.setToolTipText(StringTable.CONFIGURATION_FEATUREMODEL_DEFECT_EXPLANATION_SETTINGS_TOOLTIP);
		fDSolver = new ComboFieldEditor(SolverManager.FEATURE_MODEL_DEFECT_SOLVER, "Solver: ", getSolverNamesAndValues(), featureModelAnalysisGroup);
		fDSolver.setPage(this);
		fDSolver.setPreferenceStore(getPreferenceStore());
		fDSolver.load();
	}

	private String[][] getSolverNamesAndValues() {
		final String[][] solverNamesAndValues = new String[registeredFactories.size()][2];
		for (int i = 0; i < registeredFactories.size(); i++) {
			solverNamesAndValues[i][0] = registeredFactories.get(i).getDisplayName();
			solverNamesAndValues[i][1] = registeredFactories.get(i).getId();
		}
		return solverNamesAndValues;
	}

	@Override
	protected void performDefaults() {
		fASolver.loadDefault();
		fDSolver.loadDefault();
		super.performDefaults();
	}

	@Override
	public boolean performOk() {
		fASolver.store();
		fDSolver.store();
		return super.performOk();
	}
}
