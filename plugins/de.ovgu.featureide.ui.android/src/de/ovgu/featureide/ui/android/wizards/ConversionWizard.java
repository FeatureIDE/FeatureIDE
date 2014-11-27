package de.ovgu.featureide.ui.android.wizards;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.ui.android.AndroidUIPlugin;
import de.ovgu.featureide.munge_android.AndroidProjectConversion;

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
		setWindowTitle("Add FeatureIDE Nature to Android Project");

		// get selected project
		Object obj = selection.getFirstElement();
		IProject p = null;
		if (obj instanceof IResource) {
			IResource res = (IResource) obj;
			p = res.getProject();
		}

		page = new ConversionPage(p);
		this.selection = selection;
	}

	@Override
	public boolean performFinish() {

		Object obj = selection.getFirstElement();
		if (obj instanceof IResource) {
			if (page.hasCompositionTool()) {
				IProject project = ((IResource) obj).getProject();
				if (project.isOpen()) {
					AndroidProjectConversion.convertAndroidProject(project, page.getCompositionTool().getId(),
							page.getSourcePath(), page.getConfigPath(), page.getBuildPath());
					
					AndroidUIPlugin.getDefault().openEditor(FeatureModelEditor.ID, project.getFile("model.xml"));
				} else {
					return false;
				}
			}
			return true;
		}

		return false;
	}

	@Override
	public void addPages() {
		addPage(page);
		super.addPages();
	}
}
