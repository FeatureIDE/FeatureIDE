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

import static de.ovgu.featureide.fm.core.localization.StringTable.LOOKS_FOR_OPEN_CLAUSES_IN_THE_CNF_REPRESENTATION_OF_THE_FEATURE_MODEL_AND_HIGHLIGHTS_THE_CORRESPONDING_FEATURES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_CONFIGURATION_EDITOR_PROVIDES_FEATURE_HIGHLIGHTING_FOR_INVALID_CONFIGURATIONS_IN_ODER_TO_FIND_VALID_CONFIGURATIONS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.TRIES_TO_FIND_FEATURES_WHICH_LEAD_TO_A_VALID_CONFIGURATION_BY_SOLVING_A_SATISFIABILITY_PROBLEM_;

import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.dimacs.DIMACSFormat;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.core.preferences.CompletionPreference;
import de.ovgu.featureide.fm.core.preferences.ConstraintViewPreference;
import de.ovgu.featureide.fm.core.preferences.DIMACSOmitRootPreference;
import de.ovgu.featureide.fm.core.preferences.NonGTKFileDialogPreference;

public class FeatureIDEPreferencePage extends PreferencePage implements IWorkbenchPreferencePage {

	private Button noneButton;
	private Button openClauseButton;
	private Button contradictionButton;
	private Button constraintViewShowButton;
	private Button constraintViewAskButton;
	private Button constraintViewHideButton;
	private Button gtkWorkaroundInfoToggle;
	private Button dimacsOmitRootToggle;

	public FeatureIDEPreferencePage() {}

	public FeatureIDEPreferencePage(String title) {
		super(title);
	}

	public FeatureIDEPreferencePage(String title, ImageDescriptor image) {
		super(title, image);
	}

	@Override
	protected void performDefaults() {
		super.performDefaults();
		switch (CompletionPreference.getInstance().getDefault()) {
		case CompletionPreference.COMPLETION_NONE:
			noneButton.setSelection(true);
			openClauseButton.setSelection(false);
			contradictionButton.setSelection(false);
			break;
		case CompletionPreference.COMPLETION_OPEN_CLAUSES:
			noneButton.setSelection(false);
			openClauseButton.setSelection(true);
			contradictionButton.setSelection(false);
			break;
		case CompletionPreference.COMPLETION_ONE_CLICK:
			noneButton.setSelection(false);
			openClauseButton.setSelection(false);
			contradictionButton.setSelection(true);
			break;
		}
		switch (ConstraintViewPreference.getInstance().getDefault()) {
		case ConstraintViewPreference.ASK:
			constraintViewAskButton.setSelection(true);
			constraintViewShowButton.setSelection(false);
			constraintViewHideButton.setSelection(false);
			break;
		case ConstraintViewPreference.SHOW:
			constraintViewAskButton.setSelection(false);
			constraintViewShowButton.setSelection(true);
			constraintViewHideButton.setSelection(false);
			break;
		case ConstraintViewPreference.HIDE:
			constraintViewAskButton.setSelection(false);
			constraintViewShowButton.setSelection(false);
			constraintViewHideButton.setSelection(true);
			break;
		}
		gtkWorkaroundInfoToggle.setSelection(NonGTKFileDialogPreference.getInstance().getDefault());
		dimacsOmitRootToggle.setSelection(DIMACSOmitRootPreference.getInstance().getDefault());
	}

	@Override
	public boolean performOk() {
		if (!super.performOk()) {
			return false;
		}
		if (noneButton.getSelection()) {
			CompletionPreference.getInstance().set(CompletionPreference.COMPLETION_NONE);
		} else if (openClauseButton.getSelection()) {
			CompletionPreference.getInstance().set(CompletionPreference.COMPLETION_OPEN_CLAUSES);
		} else if (contradictionButton.getSelection()) {
			CompletionPreference.getInstance().set(CompletionPreference.COMPLETION_ONE_CLICK);
		}
		if (constraintViewAskButton.getSelection()) {
			ConstraintViewPreference.getInstance().set(ConstraintViewPreference.ASK);
		} else if (constraintViewShowButton.getSelection()) {
			ConstraintViewPreference.getInstance().set(ConstraintViewPreference.SHOW);
		} else if (constraintViewHideButton.getSelection()) {
			ConstraintViewPreference.getInstance().set(ConstraintViewPreference.HIDE);
		}
		NonGTKFileDialogPreference.getInstance().set(gtkWorkaroundInfoToggle.getSelection());
		DIMACSOmitRootPreference.getInstance().set(dimacsOmitRootToggle.getSelection());
		try {
			((DIMACSFormat) FMFormatManager.getInstance().getExtension(DIMACSFormat.ID)).setOmitDummyRoot(DIMACSOmitRootPreference.getInstance().get());
		} catch (final NoSuchExtensionException e) {
			Logger.logError(e);
		}
		return true;
	}

	@Override
	public void init(IWorkbench workbench) {}

	@Override
	protected Control createContents(Composite parent) {
		final Composite container = new Composite(parent, SWT.NULL);
		container.setLayout(new FillLayout(SWT.VERTICAL));

		final Group completionGroup = new Group(container, SWT.SHADOW_IN);
		completionGroup.setText("Configuration Completion");
		completionGroup.setLayout(new RowLayout(SWT.VERTICAL));
		completionGroup.setToolTipText(THE_CONFIGURATION_EDITOR_PROVIDES_FEATURE_HIGHLIGHTING_FOR_INVALID_CONFIGURATIONS_IN_ODER_TO_FIND_VALID_CONFIGURATIONS_);
		noneButton = new Button(completionGroup, SWT.RADIO);
		openClauseButton = new Button(completionGroup, SWT.RADIO);
		contradictionButton = new Button(completionGroup, SWT.RADIO);

		noneButton.setText("None");
		openClauseButton.setText("Check open clauses (Faster results)");
		contradictionButton.setText("Check contradiction (Better results)");

		noneButton.setToolTipText("Disable the functionality (Yields best performance for large feature models).");
		openClauseButton.setToolTipText(LOOKS_FOR_OPEN_CLAUSES_IN_THE_CNF_REPRESENTATION_OF_THE_FEATURE_MODEL_AND_HIGHLIGHTS_THE_CORRESPONDING_FEATURES_);
		contradictionButton.setToolTipText(TRIES_TO_FIND_FEATURES_WHICH_LEAD_TO_A_VALID_CONFIGURATION_BY_SOLVING_A_SATISFIABILITY_PROBLEM_);

		switch (CompletionPreference.getInstance().get()) {
		case CompletionPreference.COMPLETION_NONE:
			noneButton.setSelection(true);
			openClauseButton.setSelection(false);
			contradictionButton.setSelection(false);
			break;
		case CompletionPreference.COMPLETION_OPEN_CLAUSES:
			noneButton.setSelection(false);
			openClauseButton.setSelection(true);
			contradictionButton.setSelection(false);
			break;
		case CompletionPreference.COMPLETION_ONE_CLICK:
			noneButton.setSelection(false);
			openClauseButton.setSelection(false);
			contradictionButton.setSelection(true);
			break;
		}

		final Group constraintViewGroup = new Group(container, SWT.SHADOW_IN);
		constraintViewGroup.setText("Constraint View");
		constraintViewGroup.setLayout(new RowLayout(SWT.VERTICAL));
		constraintViewAskButton = new Button(constraintViewGroup, SWT.RADIO);
		constraintViewShowButton = new Button(constraintViewGroup, SWT.RADIO);
		constraintViewHideButton = new Button(constraintViewGroup, SWT.RADIO);

		constraintViewAskButton.setText(StringTable.CONSTRAINT_VIEW_ASK_TEXT);
		constraintViewShowButton.setText(StringTable.CONSTRAINT_VIEW_ON_TEXT);
		constraintViewHideButton.setText(StringTable.CONSTRAINT_VIEW_OFF_TEXT);

		switch (ConstraintViewPreference.getInstance().get()) {
		case ConstraintViewPreference.ASK:
			constraintViewAskButton.setSelection(true);
			constraintViewShowButton.setSelection(false);
			constraintViewHideButton.setSelection(false);
			break;
		case ConstraintViewPreference.SHOW:
			constraintViewAskButton.setSelection(false);
			constraintViewShowButton.setSelection(true);
			constraintViewHideButton.setSelection(false);
			break;
		case ConstraintViewPreference.HIDE:
			constraintViewAskButton.setSelection(false);
			constraintViewShowButton.setSelection(false);
			constraintViewHideButton.setSelection(true);
			break;
		}

		// dialog Configuration
		final Group dialogGroup = new Group(container, SWT.SHADOW_IN);
		dialogGroup.setLayout(new RowLayout(SWT.VERTICAL));
		dialogGroup.setText("Other");

		gtkWorkaroundInfoToggle = new Button(dialogGroup, SWT.CHECK);
		gtkWorkaroundInfoToggle.setText(StringTable.CONFIGURATION_DIALOGS_GTK_WORKAROUND);
		gtkWorkaroundInfoToggle.setToolTipText(StringTable.GTK_WORKAROUND_INFO_MSG);
		gtkWorkaroundInfoToggle.setSelection(NonGTKFileDialogPreference.getInstance().get());

		dimacsOmitRootToggle = new Button(dialogGroup, SWT.CHECK);
		dimacsOmitRootToggle.setText("Omit artifical root feature when saving DIMACS files");
		dimacsOmitRootToggle.setSelection(DIMACSOmitRootPreference.getInstance().get());

		return container;
	}
}
