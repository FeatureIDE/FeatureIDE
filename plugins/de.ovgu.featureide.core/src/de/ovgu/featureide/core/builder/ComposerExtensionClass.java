/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathAttribute;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.ClasspathEntry;
import org.eclipse.jdt.internal.core.JavaProject;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationWriter;

/**
 * Abstract class for FeatureIDE composer extensions with default values.
 * 
 * @author Jens Meinicke
 */
@SuppressWarnings("restriction")
public abstract class ComposerExtensionClass implements IComposerExtensionClass {

	protected static final String JAVA_NATURE = "org.eclipse.jdt.core.javanature";
	public static final IPath JRE_CONTAINER = new Path("org.eclipse.jdt.launching.JRE_CONTAINER");
	protected IFeatureProject featureProject = null;
	
	protected final static String[] JAVA_TEMPLATE = new String[]{"Java", "java", PACKAGE_PATTERN + "/**\r\n * TODO description\r\n */\r\npublic class " + CLASS_NAME_PATTERN +" {\n\n}"};
	
	public boolean initialize(IFeatureProject project) {
	
		assert (project != null) : "Invalid project given";
		featureProject = project;
		return true;
	}

	public boolean clean() {
		return true;
	}

	public void copyNotComposedFiles(IFile config, IFolder destination) {
		ArrayList<String > selectedFeatures = getSelectedFeatures(config);
		if (selectedFeatures != null)
			for (String feature : selectedFeatures) {
				IFolder folder = featureProject.getSourceFolder().getFolder(feature);
				try {
					copy(folder, destination);
				} catch (CoreException e) {
					CorePlugin.getDefault().logError(e);
				}
			}
	}
	
	private void copy(IFolder featureFolder, IFolder buildFolder) throws CoreException {
		if (!featureFolder.exists()) {
			return;
		}
		
		for (IResource res : featureFolder.members()) {
			if (res instanceof IFolder) {
				IFolder folder = buildFolder.getFolder(res.getName());
				if (!folder.exists()) {
					folder.create(false, true, null);
				}
				copy((IFolder)res, folder);
			} else if (res instanceof IFile) {
				if (!extensions().contains(res.getFileExtension())) {
					IFile file = buildFolder.getFile(res.getName());
					if (!file.exists()) {
						res.copy(file.getFullPath(), true, null);
					}
				}
			}
		}
	}

	// TODO #460 this should be done with a ConfigurationReader
	private ArrayList<String> getSelectedFeatures(IFile config) {
		File configFile = config.getRawLocation().toFile();
		return getTokenListFromFile(configFile);
	}

	/**
	 * returns a List of the tokens in file+
	 * this method is public for testing purposes 
	 * 
	 * @param file
	 * @return List of tokens
	 */
	public static ArrayList<String> getTokenListFromFile(File file) {
		ArrayList<String> list = null;
		Scanner scanner = null;

		try {
			scanner = new Scanner(file, "UTF-8");

			if (scanner.hasNext()) {
				list = new ArrayList<String>();
				while (scanner.hasNext()) {
					list.add(scanner.next());
				}

			}

		} catch (FileNotFoundException e) {
			CorePlugin.getDefault().logError(e);
		} finally {
			if(scanner!=null)scanner.close();
		}
		return list;
	}

	public LinkedHashSet<String> extensions() {
		return new LinkedHashSet<String>(0);
	}

	public boolean postAddNature(IFolder source, IFolder destination) {
		return false;
	}

	public void addCompiler(IProject project, String sourcePath,
			String configPath, String buildPath) {
		addNature(project);
		addClasspathFile(project, buildPath);
	}
	
	private void addClasspathFile(IProject project, String buildPath) {
		try {
			JavaProject javaProject = new JavaProject(project, null);
			IClasspathEntry[] oldEntries = javaProject.getRawClasspath();
			boolean sourceAdded = false;
			boolean containerAdded = false;
			/** check if entries already exist **/
			for (int i = 0; i < oldEntries.length; i++) {
				if (!sourceAdded && oldEntries[i].getEntryKind() == IClasspathEntry.CPE_SOURCE) {
					/** correct the source entry **/
					// XXX the source entry should be equivalent to the build path, 
					// but e.g. at FeatureHouse the real build path is src/config -> Builder problems
					// -> is it necessary to correct the path?
					if (oldEntries[i].getPath().toString().equals("/" + project.getName())) {
						/** necessary after creating a new FeatureIDE project **/
						oldEntries[i] = setSourceEntry(buildPath, oldEntries[i]);
					}
					/** find source entry **/
					sourceAdded = true;
				} else if (!containerAdded && oldEntries[i].getEntryKind() == IClasspathEntry.CPE_CONTAINER) {
					/** check the container entries **/
					if (oldEntries[i].getPath().equals(JRE_CONTAINER)) {
						containerAdded = true;
					}
				}
			}
			/** case: no new entries **/
			if (sourceAdded && containerAdded) {
				javaProject.setRawClasspath(oldEntries, null);
				return;
			}
			
			/** add the new entries **/
			IClasspathEntry[] entries = new IClasspathEntry[(sourceAdded ? 0 : 1) + (containerAdded ? 0 : 1) + oldEntries.length];
			System.arraycopy(oldEntries, 0, entries, 0, oldEntries.length);
			
			if (!sourceAdded) {
				entries[oldEntries.length] = getSourceEntry(buildPath);
			}
			if (!containerAdded) {
				int position = (sourceAdded ? 0 : 1) + oldEntries.length;
				entries[position] = getContainerEntry();
			}
			
			javaProject.setRawClasspath(entries, null);
		} catch (JavaModelException e) {
			CorePlugin.getDefault().logError(e);
		}		
	}

	/**
	 * Set the source path of the given <code>ClasspathEntry</code>
	 * @param buildPath The new build path
	 * @param e The entry to set
	 * @return The entry with the new source path
	 */
	public IClasspathEntry setSourceEntry(String buildPath, IClasspathEntry e) {
		return new ClasspathEntry(e.getContentKind(), e.getEntryKind(), 
				new Path(buildPath), e.getInclusionPatterns(), e.getExclusionPatterns(), 
				e.getSourceAttachmentPath(), e.getSourceAttachmentRootPath(), null, 
				e.isExported(), e.getAccessRules(), e.combineAccessRules(), e.getExtraAttributes());
	}

	/**
	 * @return A default JRE container entry
	 */
	public IClasspathEntry getContainerEntry() {
		return new ClasspathEntry(IPackageFragmentRoot.K_SOURCE, 
				IClasspathEntry.CPE_CONTAINER, JRE_CONTAINER, 
				new IPath[0], new IPath[0], null, null, null, false, null, false, new IClasspathAttribute[0]);
	}

	/**
	 * @param path The source path
	 * @return A default source entry with the given path
	 */
	public IClasspathEntry getSourceEntry(String path) {
		return new ClasspathEntry(IPackageFragmentRoot.K_SOURCE, 
				IClasspathEntry.CPE_SOURCE, new Path(path), new IPath[0], new IPath[0], 
				null, null, null, false, null, false, new IClasspathAttribute[0]);
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

	public String replaceMarker(String text, List<String> list, String packageName) {
		if (packageName.equals("")) {
			return text.replace(PACKAGE_PATTERN, "");
		} else {
			return text.replace(PACKAGE_PATTERN, "package " + packageName + ";\r\n\r\n");
		}
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
	
	public boolean refines() {
		return false;
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
	/**
	 * Creates a configuration file at the given folder
	 */
	public void buildConfiguration(IFolder folder, Configuration configuration, String congurationName) {
		try {
			if (!folder.exists()) {
				folder.create(true, false, null);
			}
			IFile configurationFile = folder.getFile(congurationName + "." + getConfigurationExtension());
			ConfigurationWriter writer = new ConfigurationWriter(configuration);
			writer.saveToFile(configurationFile);
			copyNotComposedFiles(configurationFile, folder);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}
	
	public boolean hasSourceFolder() {
		return true;
	}

	public boolean canGeneratInParallelJobs() {
		return true; 
	}
	
	public boolean showContextFieldsAndMethods() {
		return true;
	}
	
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		return null;
	}

	public boolean needColor() {
		return false;
	}
	
	public boolean hasContractComposition() {
		return false;
	}
}
