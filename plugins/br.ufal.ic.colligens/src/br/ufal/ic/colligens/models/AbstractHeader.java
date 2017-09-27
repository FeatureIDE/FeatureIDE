package br.ufal.ic.colligens.models;

import static de.ovgu.featureide.fm.core.localization.StringTable.NOT_A_VALID_FILE_C_IN;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import org.eclipse.cdt.core.model.CModelException;
import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.model.ICProject;
import org.eclipse.cdt.core.model.ISourceRoot;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.preference.IPreferenceStore;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.ProjectExplorerController;
import br.ufal.ic.colligens.util.metrics.CountDirectives;

public abstract class AbstractHeader {

	private List<String> listAllFiles = null;

	protected CountDirectives countDirectives = null;

	private ICProject project;

	protected IProgressMonitor monitor = null;

	public AbstractHeader() {
		final IPreferenceStore store = Colligens.getDefault().getPreferenceStore();
		if (!store.getBoolean("USE_INCLUDES") && !store.getBoolean("USE_STUBS")) {
			store.setValue("USE_STUBS", true);
		}
	}

	public static AbstractHeader getInstance() {
		final IPreferenceStore store = Colligens.getDefault().getPreferenceStore();
		if (!store.getBoolean("USE_INCLUDES") && !store.getBoolean("USE_STUBS")) {
			store.setValue("USE_STUBS", true);
		}

		if (store.getBoolean("USE_STUBS")) {
			return new StubsHeader();
		}
		if (store.getBoolean("USE_INCLUDES")) {
			return new PlatformHeader();
		}

		// don't return null,the 1th if
		return null;
	}

	abstract public void run() throws PlatformException;

	abstract public String getIncludePath();

	abstract public Collection<String> getIncludes();

	public ICProject getProject() {
		return project;
	}

	public void setProject(String projectName) throws PlatformException {
		project = CoreModel.getDefault().getCModel().getCProject(projectName);

		if (project == null) {
			throw new PlatformException(NOT_A_VALID_FILE_C_IN + projectName);
		}
	}

	protected List<String> filesAllProject() throws PlatformException {
		if ((listAllFiles != null) && (listAllFiles.size() > 0)) {
			return listAllFiles;
		}

		listAllFiles = new ArrayList<String>();

		try {

			final ISourceRoot sourceRoots[] = project.getSourceRoots();
			for (int i = 0; i < sourceRoots.length; i++) {
				if (!sourceRoots[i].getPath().toOSString().equals(project.getProject().getName())) {
					final ProjectExplorerController explorerController = new ProjectExplorerController();
					explorerController.addResource(sourceRoots[i].getResource());

					listAllFiles.addAll(explorerController.getListToString());
				}
			}
			if (listAllFiles.isEmpty()) {
				throw new PlatformException("Your project does not have a source folder (ex.: /src).");
			}
		} catch (final CModelException e1) {
			throw new PlatformException("Your project does not have a source folder (ex.: /src).");
		}

		countDirectives = new CountDirectives();

		countDirectives.directives.add("COLLIGENS");

		for (final Iterator<String> iterator = listAllFiles.iterator(); iterator.hasNext();) {
			final String file = iterator.next();
			try {
				countDirectives.count(file);
			} catch (final Exception e) {

				e.printStackTrace();
				throw new PlatformException("unexpected error!");
			}
		}

		return listAllFiles;
	}

	public static IFile getFile(String fileName) {
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		final IPath location = Path.fromOSString(fileName);
		return workspace.getRoot().getFileForLocation(location);
	}

	public void setMonitor(IProgressMonitor monitor) {
		this.monitor = monitor;
	}

	protected boolean monitorIsCanceled() {
		return monitor != null ? monitor.isCanceled() : false;
	}

	protected void monitorWorked(int value) {
		if (monitor == null) {
			return;
		}
		monitor.worked(value);
	}

	protected void monitorSubTask(String label) {
		if (monitor == null) {
			return;
		}
		monitor.subTask(label);
	}

	protected void monitorbeginTask(String label, int size) {
		if (monitor == null) {
			return;
		}
		monitor.beginTask(label, size);
	}

	public void refreshLocal() {
		try {
			getProject().getProject().refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());
		} catch (final CoreException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

}
