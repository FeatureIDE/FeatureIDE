/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.wizards;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.ISelection;
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
public class ConversionWizard  extends Wizard implements INewWizard {

	public static final String ID = UIPlugin.PLUGIN_ID + ".wizzard.ConversionWizzard";
	
	private ISelection selection;
	
	private ConversionPage page;

	private IStructuredSelection iSSelection;
	
	public boolean performFinish() {
		if (selection instanceof IStructuredSelection) {
			iSSelection = (IStructuredSelection)selection;
			Object obj = iSSelection.getFirstElement();
			if (obj instanceof IResource) {
				IResource res = (IResource)obj;
				if (page.hasCompositionTool()) {
					CorePlugin.setupProject(res.getProject(), page.getCompositionTool().getId()
							,page.getSourcePath(),page.getEquationsPath(),page.getBuildPath());
					UIPlugin.getDefault().openEditor(FeatureModelEditor.ID, (res.getProject()).getFile("model.xml"));
				}
				return true;
			}
		}
		return false;
	}
	/* (non-Javadoc)
	 * @see org.eclipse.jface.wizard.Wizard#addPages()
	 */
	@Override
	public void addPages() {
		//addPage(new ConversionPage(selection));
		setWindowTitle("Add FeatureIDE Nature");
		addPage(page);
		super.addPages();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchWizard#init(org.eclipse.ui.IWorkbench, org.eclipse.jface.viewers.IStructuredSelection)
	 */
	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		String project = ""; 
		if (selection instanceof IStructuredSelection) {
			iSSelection = (IStructuredSelection)selection;
			Object obj = iSSelection.getFirstElement();
			if (obj instanceof IResource) {
				IResource res = (IResource)obj;
				project = res.getProject().getName();
			}
		}
		page = new ConversionPage(" " + project);
		this.selection = selection;
	}
}
