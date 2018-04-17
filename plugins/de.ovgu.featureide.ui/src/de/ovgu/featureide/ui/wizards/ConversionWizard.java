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
package de.ovgu.featureide.ui.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADD_FEATUREIDE_NATURE;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * A Wizard to add the FeatureIDE Nature to a Project.
 *
 * @author Jens Meinicke
 * @author Sebastian Krieter
 */
public class ConversionWizard extends Wizard implements INewWizard {

	public static final String ID = UIPlugin.PLUGIN_ID + ".wizzard.ConversionWizzard";

	private ConversionPage page;

	private IProject project;

	@Override
	public boolean performFinish() {
		if (page.hasCompositionTool() && project.isOpen()) {
			CorePlugin.setupProject(project, page.getCompositionTool().getId(), page.getSourcePath(), page.getConfigPath(), page.getBuildPath(),
					page.isEnabled(page.sourcePath), page.isEnabled(page.buildPath));
			UIPlugin.getDefault().openEditor(FeatureModelEditor.ID, project.getFile("model.xml"));
			return true;
		}
		return false;
	}

	@Override
	public void addPages() {
		// addPage(new ConversionPage(selection));
		setWindowTitle(ADD_FEATUREIDE_NATURE);
		addPage(page);
		super.addPages();
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		final IResource res = SelectionWrapper.init(selection, IResource.class).getNext();
		if (res != null) {
			project = res.getProject();
			page = new ConversionPage(project);
		}
	}
}
