/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.CONFIGURATION_COLORING;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONFIGURATION_DIALOGS;
import static de.ovgu.featureide.fm.core.localization.StringTable.LOOKS_FOR_OPEN_CLAUSES_IN_THE_CNF_REPRESENTATION_OF_THE_FEATURE_MODEL_AND_HIGHLIGHTS_THE_CORRESPONDING_FEATURES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_CONFIGURATION_EDITOR_PROVIDES_FEATURE_HIGHLIGHTING_FOR_INVALID_CONFIGURATIONS_IN_ODER_TO_FIND_VALID_CONFIGURATIONS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.TRIES_TO_FIND_FEATURES_WHICH_LEAD_TO_A_VALID_CONFIGURATION_BY_SOLVING_A_SATISFIABILITY_PROBLEM_;

import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import de.ovgu.featureide.fm.core.Preferences;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.views.constraintview.util.ConstraintViewDialog;
import de.ovgu.featureide.fm.ui.wizards.NonGTKFileDialog;

public class FeatureIDEPreferencePage extends PreferencePage implements IWorkbenchPreferencePage {

	private static final SelectionListener completionSelectionListener = new SelectionListener() {

		@Override
		public void widgetSelected(SelectionEvent e) {
			Preferences.setDefaultCompletion((Integer) ((Button) e.getSource()).getData());
		}

		@Override
		public void widgetDefaultSelected(SelectionEvent e) {}
	};

	public FeatureIDEPreferencePage() {}

	public FeatureIDEPreferencePage(String title) {
		super(title);
	}

	public FeatureIDEPreferencePage(String title, ImageDescriptor image) {
		super(title, image);
	}

	@Override
	public void init(IWorkbench workbench) {}

	@Override
	protected Control createContents(Composite parent) {
		final Composite container = new Composite(parent, SWT.NULL);
		container.setLayout(new FillLayout(SWT.VERTICAL));

		final Group completionGroup = new Group(container, SWT.SHADOW_IN);
		completionGroup.setText(CONFIGURATION_COLORING);
		completionGroup.setLayout(new RowLayout(SWT.VERTICAL));
		completionGroup.setToolTipText(THE_CONFIGURATION_EDITOR_PROVIDES_FEATURE_HIGHLIGHTING_FOR_INVALID_CONFIGURATIONS_IN_ODER_TO_FIND_VALID_CONFIGURATIONS_);
		final Button noneButton = new Button(completionGroup, SWT.RADIO);
		final Button openClauseButton = new Button(completionGroup, SWT.RADIO);
		final Button contradictionButton = new Button(completionGroup, SWT.RADIO);

		noneButton.setData(Preferences.COMPLETION_NONE);
		openClauseButton.setData(Preferences.COMPLETION_OPEN_CLAUSES);
		contradictionButton.setData(Preferences.COMPLETION_ONE_CLICK);

		noneButton.setText("None");
		openClauseButton.setText("Check open clauses (Faster results)");
		contradictionButton.setText("Check contradiction (Better results)");

		noneButton.setToolTipText("Diseable the functionality (Yields best performance for large feature models).");
		openClauseButton.setToolTipText(LOOKS_FOR_OPEN_CLAUSES_IN_THE_CNF_REPRESENTATION_OF_THE_FEATURE_MODEL_AND_HIGHLIGHTS_THE_CORRESPONDING_FEATURES_);
		contradictionButton.setToolTipText(TRIES_TO_FIND_FEATURES_WHICH_LEAD_TO_A_VALID_CONFIGURATION_BY_SOLVING_A_SATISFIABILITY_PROBLEM_);

		switch (Preferences.getDefaultCompletion()) {
		case Preferences.COMPLETION_NONE:
			noneButton.setSelection(true);
			break;
		case Preferences.COMPLETION_OPEN_CLAUSES:
			openClauseButton.setSelection(true);
			break;
		case Preferences.COMPLETION_ONE_CLICK:
			contradictionButton.setSelection(true);
			break;
		}

		noneButton.addSelectionListener(completionSelectionListener);
		openClauseButton.addSelectionListener(completionSelectionListener);
		contradictionButton.addSelectionListener(completionSelectionListener);

		// dialog Configuration
		final Group dialogGroup = new Group(container, SWT.SHADOW_IN);
		dialogGroup.setLayout(new RowLayout(SWT.VERTICAL));
		dialogGroup.setText(CONFIGURATION_DIALOGS);

		final Button constraintViewRememberButton = new Button(dialogGroup, SWT.CHECK);
		constraintViewRememberButton.setText(StringTable.CONFIGURATION_DIALOGS_REMEMBER_CONSTRAINT_TEXT);
		constraintViewRememberButton.setToolTipText(StringTable.CONFIGURATION_DIALOGS_CONSTRAINT_REMEMBER_TOOLTIP);
		constraintViewRememberButton.setSelection(Boolean.valueOf(Preferences.getPref(ConstraintViewDialog.CONSTRAINT_VIEW_REMEMBER, "default")));
		constraintViewRememberButton.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent event) {
				Preferences.store(ConstraintViewDialog.CONSTRAINT_VIEW_REMEMBER, String.valueOf(constraintViewRememberButton.getSelection()));
			}
		});

		final Button constraintViewDecisionButton = new Button(dialogGroup, SWT.CHECK);
		constraintViewDecisionButton.setText(StringTable.CONFIGURATION_DIALOGS_DECISION_CONSTRAINT_TEXT);
		constraintViewDecisionButton.setToolTipText(StringTable.CONFIGURATION_DIALOGS_CONSTRAINT_DECISION_TOOLTIP);
		constraintViewDecisionButton.setSelection(Boolean.valueOf(Preferences.getPref(ConstraintViewDialog.CONSTRAINT_VIEW_DECISION, "default")));
		constraintViewDecisionButton.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent event) {
				Preferences.store(ConstraintViewDialog.CONSTRAINT_VIEW_DECISION, String.valueOf(constraintViewDecisionButton.getSelection()));
			}
		});

		final Button gtkWorkaroundInfoToggle = new Button(dialogGroup, SWT.CHECK);
		gtkWorkaroundInfoToggle.setText(StringTable.CONFIGURATION_DIALOGS_GTK_WORKAROUND);
		gtkWorkaroundInfoToggle.setToolTipText(StringTable.GTK_WORKAROUND_INFO_MSG);
		gtkWorkaroundInfoToggle.setSelection(Boolean.valueOf(Preferences.getPref(NonGTKFileDialog.WORKAROUND_INFO_REMEMBER, "false")));
		gtkWorkaroundInfoToggle.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent event) {
				Preferences.store(NonGTKFileDialog.WORKAROUND_INFO_REMEMBER, String.valueOf(gtkWorkaroundInfoToggle.getSelection()));
			}
		});

		return container;
	}
}
