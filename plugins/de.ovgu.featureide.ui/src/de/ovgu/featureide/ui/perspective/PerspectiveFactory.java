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
package de.ovgu.featureide.ui.perspective;

import static de.ovgu.featureide.fm.core.localization.StringTable.DEPRECATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.LEFT;
import static de.ovgu.featureide.fm.core.localization.StringTable.RIGHT;

import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

import de.ovgu.featureide.fm.ui.views.FeatureModelEditView;
import de.ovgu.featureide.fm.ui.views.outline.custom.Outline;
import de.ovgu.featureide.fm.ui.wizards.NewFeatureModelWizard;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.statistics.ui.FeatureStatisticsView;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.views.configMap.ConfigurationMap;
import de.ovgu.featureide.ui.wizards.NewConfigurationFileWizard;
import de.ovgu.featureide.ui.wizards.NewFeatureIDEFileWizard;
import de.ovgu.featureide.ui.wizards.NewFeatureProjectWizard;

/**
 * The factory for the FeatureIDE perspective.
 *
 * @author Christian Becker
 * @author Thomas Thuem
 * @author Christopher Sontag
 */
public class PerspectiveFactory implements IPerspectiveFactory {

	public static final String ID = UIPlugin.PLUGIN_ID + ".FeatureIDEperspective";

	@Override
	@SuppressWarnings(DEPRECATION)
	public void createInitialLayout(IPageLayout layout) {
		final String editorArea = layout.getEditorArea();

		layout.addNewWizardShortcut(NewFeatureProjectWizard.ID);
		layout.addNewWizardShortcut(NewFeatureIDEFileWizard.ID);
		layout.addNewWizardShortcut(NewConfigurationFileWizard.ID);
		layout.addNewWizardShortcut(NewFeatureModelWizard.ID);
		layout.addNewWizardShortcut("org.eclipse.ui.wizards.new.file");
		layout.addNewWizardShortcut("org.eclipse.ui.wizards.new.folder");

		final IFolderLayout left = layout.createFolder(LEFT, IPageLayout.LEFT, (float) 0.23, editorArea);
		final IFolderLayout down = layout.createFolder("down", IPageLayout.BOTTOM, (float) 0.80, editorArea);
		final IFolderLayout right = layout.createFolder(RIGHT, IPageLayout.RIGHT, (float) 0.75, editorArea);

		down.addView(CollaborationView.ID);
		down.addView(ConfigurationMap.ID);
		down.addView(FeatureModelEditView.ID);
		down.addView(FeatureStatisticsView.ID);

		down.addView(IPageLayout.ID_PROBLEM_VIEW);
		down.addView("org.eclipse.ui.console.ConsoleView");

		right.addView(Outline.ID);
		right.addView(IPageLayout.ID_OUTLINE);

		left.addView("org.eclipse.jdt.ui.PackageExplorer");
		left.addView("org.eclipse.ui.navigator.ProjectExplorer");

		layout.addShowViewShortcut(FeatureStatisticsView.ID);
		layout.addShowViewShortcut(FeatureModelEditView.ID);
		layout.addShowViewShortcut(ConfigurationMap.ID);
		layout.addShowViewShortcut(CollaborationView.ID);
		layout.addShowViewShortcut(Outline.ID);
		layout.addShowViewShortcut(IPageLayout.ID_RES_NAV);
		layout.addShowViewShortcut(IPageLayout.ID_OUTLINE);
		layout.addShowViewShortcut(IPageLayout.ID_TASK_LIST);

	}
}
