/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.builder;

import static de.ovgu.featureide.fm.core.localization.StringTable.JAVA;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.internal.runtime.InternalPlatform;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.IClasspathAttribute;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.ClasspathEntry;
import org.eclipse.jdt.internal.core.JavaProject;
import org.osgi.framework.Bundle;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.DefaultFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.JavaFileSystem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 * Abstract class for FeatureIDE composer extensions with default values.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
@SuppressWarnings(RESTRICTION)
public abstract class ComposerExtensionClass implements IComposerExtensionClass {

	public static final IPath JRE_CONTAINER = new Path("org.eclipse.jdt.launching.JRE_CONTAINER");
	public static final String NEWLINE = System.getProperty("line.separator", "\n");

	protected static final String JAVA_NATURE = "org.eclipse.jdt.core.javanature";
	protected final static String[] JAVA_TEMPLATE = new String[] { JAVA, "java", PACKAGE_PATTERN + "/**" + NEWLINE + " * TODO description" + NEWLINE + " */"
		+ NEWLINE + "public class " + CLASS_NAME_PATTERN + " {" + NEWLINE + NEWLINE + "}" };

	protected IFeatureProject featureProject = null;

	private boolean initialized = false;
	private IComposerExtension composerExtensionProxy;

	@Override
	public String getName() {
		return composerExtensionProxy.getName();
	}

	@Override
	public String getDescription() {
		return composerExtensionProxy.getDescription();
	}

	@Override
	public String getId() {
		return composerExtensionProxy.getId();
	}

	@Override
	public boolean initExtension() {
		return true;
	}

	void setComposerExtension(IComposerExtension composerExtensionProxy) {
		this.composerExtensionProxy = composerExtensionProxy;
	}

	public boolean initialize(IFeatureProject project) {
		assert (project != null) : "Invalid project given";
		featureProject = project;
		return initialized = true;
	}

	public void setFeatureProject(IFeatureProject featureProject) {
		assert (featureProject != null) : "Invalid project given";
		this.featureProject = featureProject;
	}

	@Override
	public boolean isInitialized() {
		return initialized;
	}

	@Override
	public boolean clean() {
		return true;
	}

	@Override
	public void copyNotComposedFiles(Configuration c, IFolder destination) {
		final List<IFeature> selectedFeatures = c.getSelectedFeatures();
		if (selectedFeatures != null) {
			if (destination == null) {
				destination = featureProject.getBuildFolder();
			}

			for (final IFeature feature : selectedFeatures) {
				final IFolder folder = featureProject.getSourceFolder().getFolder(feature.getName());
				try {
					if (!destination.exists()) {
						destination.create(false, true, null);
					}
					copy(folder, destination);
				} catch (final CoreException e) {
					CorePlugin.getDefault().logError(e);
				}
			}
		}
	}

	protected void copy(IFolder featureFolder, IFolder buildFolder) throws CoreException {
		if (!featureFolder.exists()) {
			return;
		}

		for (final IResource res : featureFolder.members()) {
			if (res instanceof IFolder) {
				final IFolder folder = buildFolder.getFolder(res.getName());
				if (!folder.exists()) {
					folder.create(false, true, null);
				}
				copy((IFolder) res, folder);
			} else if (res instanceof IFile) {
				if (!extensions().contains(res.getFileExtension())) {
					final IFile file = buildFolder.getFile(res.getName());
					if (!file.exists()) {
						res.copy(file.getFullPath(), true, null);
					}
				}
			}
		}
	}

	@Override
	public LinkedHashSet<String> extensions() {
		return new LinkedHashSet<String>(0);
	}

	@Override
	public boolean postAddNature(IFolder source, IFolder destination) {
		return false;
	}

	@Override
	public void addCompiler(IProject project, String sourcePath, String configPath, String buildPath) {
		addNature(project);
		addClasspathFile(project, buildPath);
	}

	private void addClasspathFile(IProject project, String buildPath) {
		try {
			final JavaProject javaProject = new JavaProject(project, null);
			final IClasspathEntry[] oldEntries = javaProject.getRawClasspath();
			boolean sourceAdded = false;
			boolean containerAdded = false;
			/** check if entries already exist **/
			for (int i = 0; i < oldEntries.length; i++) {
				if (!sourceAdded && (oldEntries[i].getEntryKind() == IClasspathEntry.CPE_SOURCE)) {
					/** correct the source entry **/
					// XXX the source entry should be equivalent to the build
					// path,
					// but e.g. at FeatureHouse the real build path is
					// src/config -> Builder problems
					// -> is it necessary to correct the path?
					if (oldEntries[i].getPath().toString().equals("/" + project.getName())) {
						/** necessary after creating a new FeatureIDE project **/
						oldEntries[i] = setSourceEntry(buildPath, oldEntries[i]);
					}
					/** find source entry **/
					sourceAdded = true;
				} else if (!containerAdded && (oldEntries[i].getEntryKind() == IClasspathEntry.CPE_CONTAINER)) {
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
			final IClasspathEntry[] entries = new IClasspathEntry[(sourceAdded ? 0 : 1) + (containerAdded ? 0 : 1) + oldEntries.length];
			System.arraycopy(oldEntries, 0, entries, 0, oldEntries.length);

			if (!sourceAdded) {
				entries[oldEntries.length] = getSourceEntry(buildPath);
			}
			if (!containerAdded) {
				final int position = (sourceAdded ? 0 : 1) + oldEntries.length;
				entries[position] = getContainerEntry();
			}

			javaProject.setRawClasspath(entries, null);
		} catch (final JavaModelException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Set the source path of the given <code>ClasspathEntry</code>
	 *
	 * @param buildPath The new build path
	 * @param e The entry to set
	 * @return The entry with the new source path
	 */
	public IClasspathEntry setSourceEntry(String buildPath, IClasspathEntry e) {
		return new ClasspathEntry(e.getContentKind(), e.getEntryKind(), new Path(buildPath), e.getInclusionPatterns(), e.getExclusionPatterns(),
				e.getSourceAttachmentPath(), e.getSourceAttachmentRootPath(), null, e.isExported(), e.getAccessRules(), e.combineAccessRules(),
				e.getExtraAttributes());
	}

	/**
	 * @return A default JRE container entry
	 */
	public IClasspathEntry getContainerEntry() {
		return new ClasspathEntry(IPackageFragmentRoot.K_SOURCE, IClasspathEntry.CPE_CONTAINER, JRE_CONTAINER, new IPath[0], new IPath[0], null, null, null,
				false, null, false, new IClasspathAttribute[0]);
	}

	/**
	 * @param path The source path
	 * @return A default source entry with the given path
	 */
	public IClasspathEntry getSourceEntry(String path) {
		return new ClasspathEntry(IPackageFragmentRoot.K_SOURCE, IClasspathEntry.CPE_SOURCE, new Path(path), new IPath[0], new IPath[0], null, null, null,
				false, null, false, new IClasspathAttribute[0]);
	}

	private void addNature(IProject project) {
		try {
			if (!project.isAccessible() || project.hasNature(JAVA_NATURE)) {
				return;
			}

			final IProjectDescription description = project.getDescription();
			final String[] natures = description.getNatureIds();
			final String[] newNatures = new String[natures.length + 1];
			System.arraycopy(natures, 0, newNatures, 0, natures.length);
			newNatures[natures.length] = JAVA_NATURE;
			description.setNatureIds(newNatures);
			project.setDescription(description, null);

		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public void buildFSTModel() {

	}

	@Override
	public ArrayList<String[]> getTemplates() {
		return new ArrayList<>(0);
	}

	@Override
	public String replaceSourceContentMarker(String fileContent, boolean refines, String packageName) {
		if (packageName.isEmpty()) {
			return fileContent.replace(PACKAGE_PATTERN, "");
		} else {
			return fileContent.replace(PACKAGE_PATTERN, "package " + packageName + ";" + NEWLINE + NEWLINE);
		}
	}

	@Override
	public void postCompile(IResourceDelta delta, IFile buildFile) {
		try {
			buildFile.setDerived(true, null);
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public int getDefaultTemplateIndex() {
		return 0;
	}

	@Override
	public boolean refines() {
		return false;
	}

	@Override
	public void postModelChanged() {

	}

	@Override
	public boolean hasFeatureFolder() {
		return true;
	}

	@Override
	public boolean hasCustomFilename() {
		return false;
	}

	@Override
	public String getConfigurationExtension() {
		return ConfigFormatManager.getInstance().getExtensions().get(0).getSuffix();
	}

	@Override
	public void buildConfiguration(IFolder folder, Configuration configuration, String configurationName) {
		try {
			if (!folder.exists()) {
				folder.create(true, true, null);
			}
			final IPersistentFormat<Configuration> format = ConfigFormatManager.getInstance().getFormatById(DefaultFormat.ID);
			final IFile configurationFile = folder.getFile(configurationName + "." + format.getSuffix());
			SimpleFileHandler.save(Paths.get(configurationFile.getLocationURI()), configuration, format);
			copyNotComposedFiles(configuration, folder);
		} catch (CoreException | NoSuchExtensionException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public boolean preBuildConfiguration() {
		return true;
	}

	@Override
	public boolean hasSourceFolder() {
		return true;
	}

	@Override
	public boolean hasSource() {
		return true;
	}

	@Override
	public boolean hasBuildFolder() {
		return true;
	}

	@Override
	public boolean canGeneratInParallelJobs() {
		return true;
	}

	@Override
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		return null;
	}

	@Override
	public boolean needColor() {
		return false;
	}

	@Override
	public boolean hasContractComposition() {
		return false;
	}

	@Override
	public boolean hasMetaProductGeneration() {
		return false;
	}

	@Override
	public String[] getCompositionMechanisms() {
		return new String[0];
	}

	@Override
	public boolean createFolderForFeatures() {
		return true;
	}

	@Override
	public boolean supportsAndroid() {
		return false;
	}

	protected boolean isPluginInstalled(String ID) {
		for (final Bundle b : InternalPlatform.getDefault().getBundleContext().getBundles()) {
			if (b.getSymbolicName().startsWith(ID)) {
				return true;
			}
		}
		return false;
	}

	protected void generateWarning(String Warning) {
		featureProject.createBuilderMarker(featureProject.getProject(), Warning, 0, IMarker.SEVERITY_WARNING);
	}

	/**
	 * Not supported until you implement it.
	 */
	@Override
	public boolean supportsMigration() {
		return false;
	}

	@Override
	public IStatus isComposable() {
		return Status.OK_STATUS;
	}

	@Override
	public <T extends IComposerObject> T getComposerObjectInstance(Class<T> c) {
		return null;
	}

	/**
	 * Creates a temporary configuration that can be used by the composition tool with the old configuration format.
	 *
	 * @param config The configuration file to read from.
	 * @return The temporary configuration file.
	 */
	public java.nio.file.Path createTemporaryConfigrationFile(IFile config) {
		String configName = config.getName();
		final int extIndex = configName.lastIndexOf('.');
		if (extIndex > 0) {
			configName = configName.substring(0, extIndex);
		}
		CorePlugin.getDefault().logInfo("create config " + configName);

		final Configuration configuration = new Configuration(featureProject.getFeatureModel(), Configuration.PARAM_LAZY);

		final ProblemList problems = SimpleFileHandler.load(Paths.get(config.getLocationURI()), configuration, ConfigFormatManager.getInstance());
		if (problems.containsError()) {
			CorePlugin.getDefault().logWarning("failed to read " + config);
			return null;
		}

		try {
			final java.nio.file.Path tempFile = Files.createTempFile(configName, '.' + new DefaultFormat().getSuffix());
			new JavaFileSystem().write(tempFile, new DefaultFormat().write(configuration).getBytes(Charset.defaultCharset()));
			tempFile.toFile().deleteOnExit();
			return tempFile;
		} catch (final IOException e) {
			CorePlugin.getDefault().logError(e);
		}

		return null;
	}

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

	@Override
	public boolean showContextFieldsAndMethods() {
		return true;
	}
}
