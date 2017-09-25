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
package de.ovgu.featureide.ui.android.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADD_FEATUREIDE_NATURE_TO_ANDROID_PROJECT;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;
import de.ovgu.featureide.munge_android.AndroidProjectConversion;
import de.ovgu.featureide.ui.android.AndroidUIPlugin;

/**
 * Wizard to add the FeatuerIDE nature to an Android project.
 *
 * @author Lars-Christian Schulz
 * @author Eric Guimatsia
 */
public class ConversionWizard extends Wizard implements INewWizard {

	private ConversionPage page;
	private IStructuredSelection selection;

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		setWindowTitle(ADD_FEATUREIDE_NATURE_TO_ANDROID_PROJECT);
		page = new ConversionPage();
		this.selection = selection;
	}

	@Override
	public boolean performFinish() {
		final SelectionWrapper<IProject> selectionWrapper = SelectionWrapper.init(selection, IProject.class);
		IProject curProject;
		while ((curProject = selectionWrapper.getNext()) != null) {
			if (curProject.isAccessible()) {
				AndroidProjectConversion.convertAndroidProject(curProject, page.getCompositionTool().getId(), page.getSourcePath(), page.getConfigPath(),
						page.getBuildPath());
				AndroidUIPlugin.getDefault().openEditor(FeatureModelEditor.ID, curProject.getFile("model.xml"));
			}
		}
		return true;
	}

	@Override
	public void addPages() {
		addPage(page);
		super.addPages();
	}
}
