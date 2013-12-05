package de.ovgu.featureide.core.mspl.popup.actions;

import java.util.Iterator;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.core.mspl.MSPLNature;

public class AddNatureAction implements IObjectActionDelegate {

	private IWorkbenchPart workbenchPart;

	/**
	 * Constructor for AddNatureAction.
	 */
	public AddNatureAction() {
		super();
	}

	/**
	 * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
	 */
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		workbenchPart = targetPart;
	}

	/**
	 * @see IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		ISelection selection = workbenchPart.getSite().getSelectionProvider()
				.getSelection();

		if (selection instanceof IStructuredSelection) {
			IStructuredSelection structuredSelection = (IStructuredSelection) selection;

			for (Iterator<?> iter = structuredSelection.iterator(); iter
					.hasNext();) {
				Object obj = iter.next();

				if (obj instanceof IAdaptable) {
					IProject project = (IProject) ((IAdaptable) obj)
							.getAdapter(IProject.class);

					if (project != null) {
						try {
							// Add MSPLNature to selected projects (should be
							// only one), from:
							// http://help.eclipse.org/indigo/index.jsp?topic=%2Forg.eclipse.platform.doc.isv%2Fguide%2FresAdv_natures.htm
							IProjectDescription description = project
									.getDescription();
							String[] natures = description.getNatureIds();
							String[] newNatures = new String[natures.length + 1];
							System.arraycopy(natures, 0, newNatures, 0,
									natures.length);
							newNatures[natures.length] = MSPLNature.NATURE_ID;
							description.setNatureIds(newNatures);
							project.setDescription(description, null);

							// create directories for MPL
							project.getFolder("MPL").create(true, true, null);
							project.getFolder("Import")
									.create(true, true, null);

							// TODO: create mpl.velvet
						} catch (CoreException e) {
							e.printStackTrace();
						}
					}
				}
			}
		}

	}

	/**
	 * @see IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	public void selectionChanged(IAction action, ISelection selection) {
	}

}
