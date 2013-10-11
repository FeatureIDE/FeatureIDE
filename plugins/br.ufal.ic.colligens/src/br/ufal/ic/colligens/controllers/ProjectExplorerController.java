package br.ufal.ic.colligens.controllers;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.cdt.core.model.CModelException;
import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.model.ICProject;
import org.eclipse.cdt.core.model.ISourceRoot;
import org.eclipse.cdt.core.model.ITranslationUnit;
import org.eclipse.cdt.internal.core.model.CContainer;
import org.eclipse.cdt.internal.core.model.SourceRoot;
import org.eclipse.core.internal.resources.Project;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.part.FileEditorInput;

import br.ufal.ic.colligens.activator.Colligens;

/**
 * @author Thiago Emmanuel
 */
@SuppressWarnings("restriction")
public class ProjectExplorerController {
	private ISelection iSelection;
	private Set<IResource> iResources;
	private IWorkbenchWindow window;

	public ProjectExplorerController() {
		iResources = new HashSet<IResource>();
	}

	/**
	 * @return
	 * @throws ProjectExplorerException
	 */
	public List<IResource> start() throws ProjectExplorerException {
		iResources.clear();

		List<IResource> iResources = new LinkedList<IResource>();

		if (iSelection instanceof IStructuredSelection) {

			IStructuredSelection selection = (IStructuredSelection) iSelection;

			@SuppressWarnings("unchecked")
			List<Object> list = selection.toList();

			for (Object object : list) {
				if (object instanceof Project) {
					ICProject project = CoreModel.getDefault().getCModel()
							.getCProject(((Project) object).getName());
					if (project != null) {
						try {
							ISourceRoot iSourceRoots[] = project
									.getSourceRoots();

							for (ISourceRoot iSourceRoot : iSourceRoots) {
								iResources.add(iSourceRoot.getResource());
							}

						} catch (CModelException e) {

						}
					}
				} else if (object instanceof SourceRoot) {
					iResources.add(((SourceRoot) object).getResource());
				} else if (object instanceof CContainer) {
					iResources.add(((CContainer) object).getResource());
				} else if (object instanceof ITranslationUnit) {
					iResources.add(((ITranslationUnit) object).getResource());
				} else if (object instanceof IFile) {
					iResources.add((IResource) object);
				} else if (object instanceof IFolder) {
					iResources.add((IResource) object);
				}
			}

		} else if (iSelection instanceof TextSelection) {
			FileEditorInput fileEditorInput = (FileEditorInput) window
					.getActivePage().getActiveEditor().getEditorInput();
			if (fileEditorInput != null) {
				iResources.add((IResource) fileEditorInput.getFile());
			}
		}

		if (iResources.isEmpty()) {
			throw new ProjectExplorerException(
					"Select a valid file or directory.");
		}
		
		return iResources;
	}

	/**
	 * @throws ProjectExplorerException
	 */
	public void run() throws ProjectExplorerException {
		List<IResource> list = start();

		for (IResource iResource : list) {
			addResource(iResource);
		}
	}

	/**
	 * @return list containing the file paths
	 */
	public List<String> getListToString() {
		List<String> resourcesAsString = new LinkedList<String>();
		for (IResource resource : iResources) {
			// adds .c and .h files only
			resourcesAsString.add(resource.getLocation().toString());
		}
		return resourcesAsString;
	}

	public void setWindow(IWorkbenchWindow window) {
		this.window = window;
		this.iSelection = window.getSelectionService().getSelection();
	}

	public void setSelection(ISelection selection) {
		this.iSelection = selection;
	}

	public List<IResource> getList() {
		return new LinkedList<IResource>(iResources);
	}

	public void addResource(IResource iResource) {
		if (iResource instanceof IFile) {
			// adds .c and .h files only
			if (iResource.getLocation().toString().trim().endsWith(".c")
					|| iResource.getLocation().toString().trim().endsWith(".h")) {
				iResources.add(iResource);
			}
		} else if (iResource instanceof IFolder) {
			try {
				for (IResource res : ((IFolder) iResource).members()) {
					addResource(res);
				}
			} catch (CoreException e) {
				Colligens.getDefault().logError(e);
				e.printStackTrace();
			}
		}
	}
}
