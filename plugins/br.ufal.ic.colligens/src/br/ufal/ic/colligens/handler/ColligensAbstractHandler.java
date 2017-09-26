package br.ufal.ic.colligens.handler;

import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;

import java.util.Iterator;

import org.eclipse.cdt.core.model.ITranslationUnit;
import org.eclipse.cdt.internal.core.model.CContainer;
import org.eclipse.cdt.internal.core.model.SourceRoot;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.internal.resources.Project;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
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

@SuppressWarnings(RESTRICTION)
public abstract class ColligensAbstractHandler extends AbstractHandler {

	private static ISelection selection = null;
	private static boolean enabled = false;

	@Override
	public boolean isEnabled() {
		ISelection selection = null;
		try {
			selection = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getSelection();

			if ((ColligensAbstractHandler.selection != null) && ColligensAbstractHandler.selection.equals(selection)) {
				return enabled;
			}
			if (selection instanceof TextSelection) {
				ColligensAbstractHandler.selection = selection;
				final FileEditorInput fileEditorInput =
					(FileEditorInput) PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor().getEditorInput();

				enabled = ((fileEditorInput != null)
					&& (fileEditorInput.getFile().getFileExtension().equals("h") || fileEditorInput.getFile().getFileExtension().equals("c"))
					&& fileEditorInput.getFile().getProject().hasNature("de.ovgu.featureide.core.featureProjectNature"));

				return enabled;

			} else if (selection instanceof IStructuredSelection) {
				ColligensAbstractHandler.selection = selection;
				final IStructuredSelection extended = (IStructuredSelection) selection;
				for (final Iterator<?> iterator = extended.iterator(); iterator.hasNext();) {
					final Object object = iterator.next();
					if (isValid(object)) {
						enabled = true;
						return enabled;
					}
				}

			}
		} catch (final Exception e) {
			enabled = false;
			return enabled;
		}
		enabled = false;
		return enabled;
	}

	private boolean isValid(Object object) throws CoreException {
		IProject project = null;
		boolean isvalid = false;
		if (object instanceof Project) {
			project = (Project) object;
			isvalid = project.isOpen();
		} else if (object instanceof SourceRoot) {
			project = ((SourceRoot) object).getCProject().getProject();
			isvalid = true;
		} else if (object instanceof CContainer) {
			project = ((CContainer) object).getCProject().getProject();
			final IResource resource = ((CContainer) object).getResource();
			isvalid = isResource(resource);
		} else if (object instanceof ITranslationUnit) {
			final ITranslationUnit iTranslationUnit = (ITranslationUnit) object;
			project = iTranslationUnit.getCProject().getProject();
			isvalid = isResource(iTranslationUnit.getResource());
		}

		if (project != null) {
			return (project.hasNature("de.ovgu.featureide.core.featureProjectNature") && isvalid);
		}
		return false;
	}

	private boolean isResource(IResource iResource) {
		if (iResource instanceof IFile) {
			// adds .c and .h files only
			if (iResource.getLocation().toString().trim().endsWith(".c") || iResource.getLocation().toString().trim().endsWith(".h")) {
				return true;
			}
		} else if (iResource instanceof IFolder) {
			try {
				for (final IResource res : ((IFolder) iResource).members()) {
					return isResource(res);

				}
			} catch (final CoreException e) {
				return false;
			}
		}
		return false;
	}

	protected static final boolean saveAll() {
		final IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
		return IDE.saveAllEditors(new IResource[] { workspaceRoot }, true);
	}
}
