package de.ovgu.featureide.cloneanalysis.pmd;

import java.io.FilenameFilter;
import java.io.IOException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import net.sourceforge.pmd.cpd.CPD;
import net.sourceforge.pmd.cpd.CPDConfiguration;
import net.sourceforge.pmd.cpd.LanguageFactory;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;

public abstract class DefaultCloneAnalyzerAdapter<Tool> implements ICloneAnalyzerAdapter<Tool> {
	protected Tool analysisTool;

	private final FilenameFilter filter;

	protected DefaultCloneAnalyzerAdapter(final FilenameFilter filter) {
		this.filter = filter;
	}

	/**
	 * Gets the {@link IResource}s from the {@link IStructuredSelection} and
	 * registers them with the {@link #analysisTool} using
	 * {@link #registerWithAnalysisTool(Set)}.
	 * 
	 * @param currentSelection
	 *            An {@link IStructuredSelection} which contains a number of
	 *            folders or files to be analyzed.
	 * @see #registerWithAnalysisTool(Set)
	 */
	public void addResourcesFromSelection(IStructuredSelection currentSelection) {
		Set<IResource> files = new HashSet<IResource>();
		Iterator<?> iterator = currentSelection.iterator();
		while (iterator.hasNext()) {
			Object selectedObject = iterator.next();
			IResource file = null;

			if (selectedObject instanceof IResource)
				file = (IResource) selectedObject;
			else if (selectedObject instanceof IAdaptable)
				file = (IResource) ((IAdaptable) selectedObject).getAdapter(IResource.class);

			if (files != null)
				files.add(file);
		}
		registerWithAnalysisTool(files);
	}

	/**
	 * Adds a projects resources to the {@link #analysisTool}. For
	 * {@link IFeatureProject}s, only files in their feature folders will be
	 * added to the {@link #analysisTool}
	 * 
	 * @param project
	 *            an {@link IFeatureProject}.
	 * @throws IOException
	 */
	public void addProjectToAnalysis(IProject project) {
		IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		if (featureProject != null) {
			registerContainerRecursively(featureProject.getSourceFolder());
		} else
			registerContainerRecursively(project);

	}

	/**
	 * Adds all {@link IResource}s in the set to the {@link CPD} tool, by using
	 * its {@link CPD#addRecursively(String)} method.
	 * 
	 * @param resources
	 *            A set of {@link IResource}s.
	 * @throws IOException
	 *             if the folder does not exist.
	 */
	protected void registerWithAnalysisTool(Set<IResource> resources) {
		for (IResource resource : resources) {
			if (resource instanceof IFolder)
				registerContainerRecursively(((IFolder) resource));
			if (resource instanceof IProject)
				addProjectToAnalysis((IProject) resource);
		}
	}

	protected abstract void registerContainerRecursively(IContainer container);

	/**
	 * Returns a {@link CPDConfiguration} with <br>
	 * <br>
	 * language = java <br>
	 * debug = false <br>
	 * minTileSize = 10 <br>
	 * renderer = xml
	 * 
	 * @return a default {@link CPDConfiguration}
	 */
	protected CPDConfiguration createDefaultConfiguration() {
		CPDConfiguration config = new CPDConfiguration() {
			@Override
			public FilenameFilter filenameFilter() {
				return filter;
			}
		};

		config.setLanguage(LanguageFactory.createLanguage("java"));
		config.setDebug(false);
		config.setMinimumTileSize(10);
		config.setRendererName("xml");

		return config;
	}

}