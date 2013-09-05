package br.ufal.ic.colligens.actions;

import org.eclipse.cdt.core.model.ITranslationUnit;
import org.eclipse.cdt.internal.core.model.CContainer;
import org.eclipse.cdt.internal.core.model.SourceRoot;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.ide.IDE;

public abstract class PluginActions implements IWorkbenchWindowActionDelegate {
	protected IWorkbenchWindow window;
	protected IStructuredSelection selection;

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		// TODO Auto-generated method stub

		try {
			if (selection instanceof IStructuredSelection) {
				IStructuredSelection extended = (IStructuredSelection) selection;
				this.selection = extended;
				Object object = extended.getFirstElement();
				if (object instanceof SourceRoot) {
					action.setEnabled(true);
				} else if (object instanceof CContainer) {
					action.setEnabled(true);
				} else if (object instanceof ITranslationUnit) {
					action.setEnabled(true);
				} else if (object instanceof IFile || object instanceof IFolder) {
					action.setEnabled(isResource((IResource) object));
				} else {
					action.setEnabled(false);
				}
			}
		} catch (Exception e) {
			// TODO: handle exception
		}
	}

	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

	@Override
	public void init(IWorkbenchWindow window) {
		this.window = window;
	}

	private boolean isResource(IResource iResource) {
		if (iResource instanceof IFile) {
			// adds .c and .h files only
			if (iResource.getLocation().toString().trim().endsWith(".c")
					|| iResource.getLocation().toString().trim().endsWith(".h")) {
				return true;
			}
		} else if (iResource instanceof IFolder) {
			try {
				for (IResource res : ((IFolder) iResource).members()) {
					if (isResource(res)) {
						return true;
					}

				}
			} catch (CoreException e) {

			}
		}
		return false;
	}

	protected static boolean saveAll() {
		IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
		return IDE.saveAllEditors(new IResource[] { workspaceRoot }, true);
	}
}
