package br.ufal.ic.colligens.controllers;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.cdt.core.model.ITranslationUnit;
import org.eclipse.cdt.internal.core.model.CContainer;
import org.eclipse.cdt.internal.core.model.SourceRoot;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;

import br.ufal.ic.colligens.activator.Colligens;

/**
 * @author Thiago Emmanuel
 */
@SuppressWarnings("restriction")
public class ProjectExplorerController {
	private IStructuredSelection selection;
	private Set<IResource> iResources;

	public ProjectExplorerController() {
		iResources = new HashSet<IResource>();
	}

	public void setWindow(IWorkbenchWindow window) {
		//
		this.selection = (IStructuredSelection) window.getSelectionService()
				.getSelection("org.eclipse.ui.navigator.ProjectExplorer");
		if (this.selection == null) {
			this.selection = (IStructuredSelection) window
					.getSelectionService().getSelection(
							"org.eclipse.jdt.ui.PackageExplorer");
		}
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

	/**
	 * @return
	 * @throws ProjectExplorerException
	 */
	public List<IResource> start() throws ProjectExplorerException {
		
		iResources.clear();
		
		if (selection == null) {
			throw new ProjectExplorerException("Select a valid file or directory.");
		}

		List<IResource> iResources = new LinkedList<IResource>();

		@SuppressWarnings("unchecked")
		List<Object> list = selection.toList();

		for (Object object : list) {
			if (object instanceof SourceRoot) {
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

		if (iResources.isEmpty()) {
			throw new ProjectExplorerException("Select a valid file or directory.");
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
}
