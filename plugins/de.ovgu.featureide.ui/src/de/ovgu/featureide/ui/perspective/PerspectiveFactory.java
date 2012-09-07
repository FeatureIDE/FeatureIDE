/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.ui.perspective;

import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

import de.ovgu.featureide.fm.ui.views.FeatureModelEditView;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.views.collaboration.outline.CollaborationOutline;
import de.ovgu.featureide.ui.wizards.NewConfigurationFileWizard;
import de.ovgu.featureide.ui.wizards.NewFeatureIDEFileWizard;
import de.ovgu.featureide.ui.wizards.NewFeatureProjectWizard;

/**
 * The factory for the FeatureIDE perspective.
 * 
 * @author Christian Becker
 * @author Thomas Thuem
 */
public class PerspectiveFactory implements IPerspectiveFactory {

	public static final String ID = UIPlugin.PLUGIN_ID
			+ ".FeatureIDEperspective";

	@SuppressWarnings("deprecation")
	public void createInitialLayout(IPageLayout layout) {
		String editorArea = layout.getEditorArea();

		layout.addNewWizardShortcut(NewFeatureProjectWizard.ID);
		
		layout.addNewWizardShortcut(NewFeatureIDEFileWizard.ID);
		layout.addNewWizardShortcut(NewConfigurationFileWizard.ID);
		layout.addNewWizardShortcut("org.eclipse.ui.wizards.new.file");
		layout.addNewWizardShortcut("org.eclipse.ui.wizards.new.folder");
		
		IFolderLayout left = layout.createFolder("left", IPageLayout.LEFT,
				(float) 0.23, editorArea);
		IFolderLayout down = layout.createFolder("down", IPageLayout.BOTTOM,
				(float) 0.80, editorArea);
		IFolderLayout right = layout.createFolder("right", IPageLayout.RIGHT,
				(float) 0.75, editorArea);

		down.addView(CollaborationView.ID);
		down.addView(FeatureModelEditView.ID);
		
		down.addView(IPageLayout.ID_PROBLEM_VIEW);
		down.addView("org.eclipse.ui.console.ConsoleView");
		
		right.addView(CollaborationOutline.ID);
		right.addView(IPageLayout.ID_OUTLINE);

		left.addView("org.eclipse.jdt.ui.PackageExplorer");

		layout.addShowViewShortcut(FeatureModelEditView.ID);
		layout.addShowViewShortcut(CollaborationView.ID);
		layout.addShowViewShortcut(CollaborationOutline.ID);
		layout.addShowViewShortcut(IPageLayout.ID_RES_NAV);
		layout.addShowViewShortcut(IPageLayout.ID_OUTLINE);
		layout.addShowViewShortcut(IPageLayout.ID_TASK_LIST);		
	}
}
