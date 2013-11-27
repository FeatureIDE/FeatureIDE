package br.ufal.ic.colligens.handler;

import org.eclipse.cdt.core.model.ITranslationUnit;
import org.eclipse.cdt.internal.core.model.CContainer;
import org.eclipse.cdt.internal.core.model.SourceRoot;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.internal.resources.Project;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.part.FileEditorInput;

@SuppressWarnings("restriction")
public abstract class ColligensAbstractHandler extends AbstractHandler {
	private ISelection selection = null;
	private boolean enabled = false;

	@Override
	public boolean isEnabled() {
		ISelection selection = null;
		try {
			selection = PlatformUI.getWorkbench().getActiveWorkbenchWindow()
					.getActivePage().getSelection();

			if (this.selection != null & !selection.equals(selection)) {
				return enabled;
			}

			if (selection instanceof TextSelection) {
				this.selection = selection;
				FileEditorInput fileEditorInput = (FileEditorInput) PlatformUI
						.getWorkbench().getActiveWorkbenchWindow()
						.getActivePage().getActiveEditor().getEditorInput();
				if (fileEditorInput != null
						&& (fileEditorInput.getFile().getFileExtension()
								.equals("h") || fileEditorInput.getFile()
								.getFileExtension().equals("c"))) {
					enabled = true;
					return enabled;
				}

			} else if (selection instanceof IStructuredSelection) {
				this.selection = selection;
				IStructuredSelection extended = (IStructuredSelection) selection;
				Object object = extended.getFirstElement();

				if (object instanceof Project) {
					if (((Project) object).isOpen()) {
						enabled = true;
						return enabled;
					}
				} else if (object instanceof SourceRoot
						|| object instanceof CContainer
						|| object instanceof ITranslationUnit) {
					enabled = true;
					return enabled;
				} else if (object instanceof IFile || object instanceof IFolder) {
					return isResource((IResource) object);
				}
			}
		} catch (Exception e) {
			enabled = false;
			return enabled;
		}
		enabled = false;
		return enabled;
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

	protected static final boolean saveAll() {
		IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
		return IDE.saveAllEditors(new IResource[] { workspaceRoot }, true);
	}
}
