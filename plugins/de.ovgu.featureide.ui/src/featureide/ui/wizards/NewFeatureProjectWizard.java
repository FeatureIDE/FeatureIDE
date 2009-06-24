/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.ui.wizards;

import org.eclipse.ui.wizards.newresource.BasicNewProjectResourceWizard;

import featureide.core.CorePlugin;
import featureide.fm.ui.editors.FeatureModelEditor;
import featureide.ui.UIPlugin;

/**
 * A creation wizard for Jak projects that adds the Jak nature after creation.
 * 
 * @author Marcus Leich
 * @author Thomas Thüm
 * @author Tom Brosch
 * @author Janet Feigenspan
 */
public class NewFeatureProjectWizard extends BasicNewProjectResourceWizard {

	public static final String ID = UIPlugin.PLUGIN_ID + ".FeatureProjectWizard";
	
	private NewFeatureProjectPage page;
	
	@Override
	public void addPages() {
		page = new NewFeatureProjectPage();
		addPage(page);
		super.addPages();
	}

	public boolean performFinish() {
		if (!super.performFinish())
			return false;
		if (page.hasCompositionTool()) {
			CorePlugin.setupFeatureProject(getNewProject(), page.getCompositionTool().getId());
			UIPlugin.getDefault().openEditor(FeatureModelEditor.ID, getNewProject().getFile("model.m"));
		}
		return true;
	}

}
// public class NewFeatureProjectWizard extends Wizard implements INewWizard {
//	
// private BasicNewProjectResourceWizard wizard;
// private NewFeatureProjectPage page;
// private ISelection selection;
// WizardDialog dialog;
//
// public NewFeatureProjectWizard () {
// wizard = new BasicNewProjectResourceWizard();
// wizard.init(PlatformUI.getWorkbench(), null);
// wizard.addPages();
// // dialog = new WizardDialog(getShell(), wizard);
// // dialog.open();
// }
//
// @Override
// public boolean performFinish() {
// System.out.println("piep");
// // FeatureProject featureProject = new
// FeatureProject(wizard.getNewProject());
//		
// if (!wizard.performFinish())
// return false;
// // wizard.dispose();
// addJakNatureToProject(wizard.getNewProject());
// return true;
// }
//
// public void addPages(){
// page = new NewFeatureProjectPage(selection);
// addPage(page);
// }
//
// private void addJakNatureToProject(IProject project) {
// try {
// //check if the nature was already added
// if (!project.isAccessible() || project.hasNature(JakNature.NATURE_ID))
// return;
//	  	
// //add the jak nature
// System.out.println("Add JakNature to " + project.getName());
// IProjectDescription description = project.getDescription();
// String[] natures = description.getNatureIds();
// String[] newNatures = new String[natures.length + 1];
// System.arraycopy(natures, 0, newNatures, 0, natures.length);
// newNatures[natures.length] = JakNature.NATURE_ID;
// description.setNatureIds(newNatures);
// project.setDescription(description, null);
// } catch (CoreException e) {
// e.printStackTrace();
// }
// }
//
// @Override
// public void init(IWorkbench workbench, IStructuredSelection selection) {
// this.selection = selection;
// }
//
// }
//	>>>>>>> .merge-right.r741
