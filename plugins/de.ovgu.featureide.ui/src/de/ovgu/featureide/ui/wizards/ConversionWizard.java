/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.wizards;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * A Wizard to add the FeatureIDE Nature to a Project.
 * 
 * @author Jens Meinicke
 */
public class ConversionWizard extends Wizard implements INewWizard {

	public static final String ID = UIPlugin.PLUGIN_ID
			+ ".wizzard.ConversionWizzard";

	private ConversionPage page;

	private IStructuredSelection selection;

	public boolean performFinish() {

		Object obj = selection.getFirstElement();
		if (obj instanceof IResource) {
			if (page.hasCompositionTool()) {
				IProject project = ((IResource) obj).getProject();
				if (project.isOpen()) {
					CorePlugin.setupProject(project, page
							.getCompositionTool().getId(), page.getSourcePath(),
							page.getConfigPath(), page.getBuildPath());
					UIPlugin.getDefault().openEditor(FeatureModelEditor.ID,
							project.getFile("model.xml"));
				} else {
					return false;
				}
			}
			return true;
		}

		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.wizard.Wizard#addPages()
	 */
	@Override
	public void addPages() {
		// addPage(new ConversionPage(selection));
		setWindowTitle("Add FeatureIDE Nature");
		addPage(page);
		super.addPages();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.IWorkbenchWizard#init(org.eclipse.ui.IWorkbench,
	 * org.eclipse.jface.viewers.IStructuredSelection)
	 */
	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		String project = "";

		Object obj = selection.getFirstElement();
		IProject p = null;
		if (obj instanceof IResource) {
			IResource res = (IResource) obj;
			p = res.getProject();
			project = p.getName();
		}

		page = new ConversionPage(" " + project, p);
		this.selection = selection;
	}
}
