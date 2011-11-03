/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.core.builder;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationWriter;

/**
 * Abstract class for FeatureIDE composer extensions with default values.
 * 
 * @author Jens Meinicke
 */
public abstract class ComposerExtensionClass implements IComposerExtensionClass {

	protected static final String JAVA_NATURE = "org.eclipse.jdt.core.javanature";
	protected IFeatureProject featureProject = null;
	
	public boolean initialize(IFeatureProject project) {
	
		assert (project != null) : "Invalid project given";
		featureProject = project;
		return true;
	}

	public boolean clean() {
		return true;
	}

	public boolean copyNotComposedFiles() {
		return false;
	}

	public ArrayList<String> extensions() {
		return new ArrayList<String>();
	}

	public boolean postAddNature(IFolder source, IFolder destination) {
		return false;
	}

	public void addCompiler(IProject project, String sourcePath,
			String configPath, String buildPath) {
		addNature(project);
		addClasspathFile(project, sourcePath, configPath, buildPath);
	}
	
	private void addClasspathFile(IProject project, String sourcePath,
			String configPath, String buildPath) {
		IFile iClasspathFile = project.getFile(".classpath");
		if (!iClasspathFile.exists()) {
			try {
				String text = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" + 
			 				  "<classpath>\n" +  
			 				  "\t<classpathentry kind=\"src\" path=\"" + buildPath + "\"/>\n" + 
			 				  "\t<classpathentry kind=\"con\" path=\"org.eclipse.jdt.launching.JRE_CONTAINER\"/>\r\n" + 
			 				  "\t<classpathentry kind=\"output\" path=\"bin\"/>\n" + 
			 				  "</classpath>"; 
				InputStream source = new ByteArrayInputStream(text.getBytes());
				iClasspathFile.create(source, true, null);
			} catch (CoreException e) {
				CorePlugin.getDefault().logError(e);
			}

		}
	}

	private void addNature(IProject project) {
		try {
			if (!project.isAccessible() || project.hasNature(JAVA_NATURE))
				return;

			IProjectDescription description = project.getDescription();
			String[] natures = description.getNatureIds();
			String[] newNatures = new String[natures.length + 1];
			System.arraycopy(natures, 0, newNatures, 0, natures.length);
			newNatures[natures.length] = JAVA_NATURE;
			description.setNatureIds(newNatures);
			project.setDescription(description, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	public void buildFSTModel() {
		
	}

	public ArrayList<String[]> getTemplates() {
		return null;
	}

	public String replaceMarker(String text, List<String> list) {
		return text;
	}

	@SuppressWarnings("deprecation")
	public void postCompile(IResourceDelta delta, IFile buildFile) {
		try {
			buildFile.setDerived(true);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	public int getDefaultTemplateIndex() {
		return 0;
	}

	public void postModelChanged() {

	}

	public boolean hasFeatureFolder() {
		return true;
	}
	
	public boolean hasFeatureFolders() {
		return true;
	}

	public boolean hasCustomFilename() {
		return false;
	}

	public String getConfigurationExtension() {
		return CorePlugin.getDefault().getConfigurationExtensions().getFirst();
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionClass#buildConfiguration(org.eclipse.core.resources.IFolder, de.ovgu.featureide.fm.core.configuration.Configuration)
	 */
	/*
	 * Creates a configuration file at the given folder
	 */
	public void buildConfiguration(IFolder folder, Configuration configuration) {
		try {
			if (!folder.exists()) {
				folder.create(true, false, null);
			}
			IFile configurationFile = folder.getFile(folder.getName() + getConfigurationExtension());
			ConfigurationWriter writer = new ConfigurationWriter(configuration);
			writer.saveToFile(configurationFile);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}
}
