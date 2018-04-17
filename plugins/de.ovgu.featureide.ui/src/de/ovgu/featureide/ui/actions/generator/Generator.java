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
package de.ovgu.featureide.ui.actions.generator;

import static de.ovgu.featureide.fm.core.localization.StringTable.ERROR_IN_CONFIGURATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_GENERATOR_NR_;
import static de.ovgu.featureide.fm.core.localization.StringTable.WILL_BE_RESTARTED_;

import java.util.ArrayList;
import java.util.List;

import javax.annotation.CheckForNull;

import org.eclipse.core.internal.resources.Workspace;
import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.ClasspathEntry;
import org.eclipse.jdt.internal.core.JavaProject;

import de.ovgu.featureide.core.builder.ExtensibleFeatureProjectBuilder;
import de.ovgu.featureide.core.builder.FeatureProjectNature;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.builder.preprocessor.PPComposerExtensionClass;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * This {@link Job} builds all configurations of the corresponding {@link ConfigurationBuilder}
 *
 * @author Jens Meinicke
 */
@SuppressWarnings(RESTRICTION)
public class Generator extends Thread implements IConfigurationBuilderBasics {

	protected static final String JAVA_NATURE = "org.eclipse.jdt.core.javanature";

	/**
	 * A counter that shows how many configurations are built by this job
	 */
	int generated = 0;

	/**
	 * The builder containing this job
	 */
	ConfigurationBuilder builder;

	/**
	 * The number of this job.
	 */
	public int nr;

	@CheckForNull
	private JavaCompiler compiler;

	private TestRunner testRunner;

	private BuilderConfiguration configuration;

	private static boolean JUNIT_INSTALLED = Platform.getBundle("org.junit") != null;

	/**
	 *
	 * @param nr The number of the job
	 * @param builder The {@link ConfigurationBuilder} containing the {@link Generator}
	 */
	public Generator(int nr, ConfigurationBuilder builder) {
		this.nr = nr;
		this.builder = builder;
		if (!builder.createNewProjects) {
			try {
				if (builder.featureProject.getProject().hasNature(JAVA_NATURE)) {
					compiler = new JavaCompiler(nr, this);
					if (JUNIT_INSTALLED) {
						testRunner = new TestRunner(compiler.tmp, builder.testResults, builder);
					}
				}
			} catch (final CoreException e) {
				UIPlugin.getDefault().logError(e);
			} catch (final Exception e2) {
				System.out.println(e2);
			} catch (final Error e3) {
				System.out.println(e3);
			}
		}
	}

	/**
	 * Generates the configurations of CongfigurationBuilder.configurations
	 */
	@Override
	public void run() {
		try {
			while (true) {
				synchronized (this) {
					if (builder.cancelGeneratorJobs) {
						builder.generatorJobs.remove(this);
						return;
					}
					if (builder.sorter.getBufferSize() == 0) {
						while ((builder.sorter.getBufferSize() == 0) || !builder.sorter.isSorted()) {
							/** the job waits for a new configuration to build **/
							try {
								Thread.sleep(1000);
								if (((builder.sorter.getBufferSize() == 0) && builder.finish) || builder.cancelGeneratorJobs) {
									return;
								}
							} catch (final InterruptedException e) {
								UIPlugin.getDefault().logError(e);
							}
						}
					}
				}
				configuration = builder.getConfiguration();
				if (configuration == null) {
					continue;
				}
				final String name = configuration.getName();
				if (builder.createNewProjects) {
					final String separator;
					switch (builder.buildType) {
					case ALL_CURRENT:
						separator = SEPARATOR_CONFIGURATION;
						break;
					case ALL_VALID:
						separator = SEPARATOR_VARIANT;
						break;
					case INTEGRATION:
						separator = SEPARATOR_INTEGRATION;
						break;
					case RANDOM:
						separator = SEPARATOR_RANDOM;
						break;
					case T_WISE:
						separator = SEPARATOR_T_WISE;
						break;
					default:
						throw new RuntimeException(builder.buildType + " not supported");
					}
					buildConfiguration(builder.featureProject.getProjectName() + separator + name, configuration);
				} else {
					builder.featureProject.getComposer().buildConfiguration(builder.folder.getFolder(name), configuration, name);
				}

				if (compiler != null) {
					compiler.compile(configuration);
					if (builder.runTests) {
						if (JUNIT_INSTALLED) {
							testRunner.runTests(configuration);
						}
					}
				}

				builder.builtConfiguration();
			}
		} catch (final Exception e) {
			UIPlugin.getDefault().logError(ERROR_IN_CONFIGURATION + configuration, e);
			/**
			 * If there is any build error the configuration will be built again. And because this job is terminated a new one will be created.
			 */
			UIPlugin.getDefault().logWarning(THE_GENERATOR_NR_ + nr + WILL_BE_RESTARTED_);
			builder.createNewGenerator(nr);
		} finally {
			builder.generatorJobs.remove(this);
		}
		return;
	}

	/**
	 * Builds the configuration in a new project with the given name.
	 *
	 * @param name The name of the new project
	 */
	void buildConfiguration(String name, Configuration configuration) {
		final IPath p2 = new Path("/" + name);
		final ConfigurationProject project = new ConfigurationProject(p2, (Workspace) builder.featureProject.getProject().getWorkspace());
		try {
			if (!project.exists()) {
				project.create(null);
			}
			project.open(null);
			setDescription(project);
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
		List<String> srcPaths = new ArrayList<>(1);
		srcPaths.add(builder.featureProject.getBuildPath());
		try {
			if (project.hasNature(JAVA_NATURE)) {
				srcPaths = setClassPath(project);
			}
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
		}

		final IComposerExtensionClass composer = builder.featureProject.getComposer();
		for (final String src : srcPaths) {
			final IFolder buildFolder = builder.featureProject.getBuildFolder();
			final IPath buildFolderPath = buildFolder.getFullPath().makeRelativeTo(builder.featureProject.getProject().getFullPath());
			if (src.equals(buildFolderPath.toString())) {
				// build files
				final IFolder sourceFolder = project.getFolder(src);
				composer.buildConfiguration(sourceFolder, configuration, name);
				if (composer instanceof PPComposerExtensionClass) {
					((PPComposerExtensionClass) composer).postProcess(sourceFolder);
				}
			} else {
				// copy files of further source folder
				final IFolder srcFolder = builder.featureProject.getProject().getFolder(src);
				final IFolder dstFolder = project.getFolder(src);
				try {
					srcFolder.copy(dstFolder.getFullPath(), true, null);
				} catch (final CoreException e) {
					UIPlugin.getDefault().logError(e);
				}

			}
		}
		try {
			final IFile modelFile = builder.featureProject.getModelFile();
			modelFile.copy(project.getFile(modelFile.getName()).getFullPath(), true, null);
			project.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * Sets the classpath entries for the newly created project
	 *
	 * @param p The new project
	 * @return
	 */
	// TODO remove redundant calculations for each configuration
	// TODO copy settings
	private List<String> setClassPath(IProject p) {
		final List<String> sourcePaths = new ArrayList<>();
		final JavaProject baseProject = new JavaProject(builder.featureProject.getProject(), null);
		final JavaProject newProject = new JavaProject(p, null);
		try {
			final IClasspathEntry[] entries = baseProject.getRawClasspath().clone();
			for (int i = 0; i < entries.length; i++) {
				// set source entry
				final IClasspathEntry e = entries[i];
				if (entries[i].getEntryKind() == IClasspathEntry.CPE_SOURCE) {
					final String srcPath = e.getPath().removeFirstSegments(1).toOSString();
					sourcePaths.add(srcPath);
					entries[i] = new ClasspathEntry(e.getContentKind(), e.getEntryKind(), new Path(srcPath), e.getInclusionPatterns(), e.getExclusionPatterns(),
							e.getSourceAttachmentPath(), e.getSourceAttachmentRootPath(), null, e.isExported(), e.getAccessRules(), e.combineAccessRules(),
							e.getExtraAttributes());
				} else if (e.getEntryKind() == IClasspathEntry.CPE_LIBRARY) {
					// set the library entries and copy the libraries
					// which are direct at the old projects folder
					IPath path = e.getPath().removeFirstSegments(1);
					final IProject project = builder.featureProject.getProject();
					IFile file = project.getFile(path);
					if (!file.exists()) {
						path = e.getPath();
						file = project.getFile(path);
						if (!file.exists()) {
							continue;
						}
					}
					createLibFolder(p.getFile(path).getParent());
					final IFile destination = p.getFile(e.getPath().removeFirstSegments(1));
					if (!destination.exists()) {
						file.copy(destination.getFullPath(), true, null);
					}
					entries[i] = new ClasspathEntry(e.getContentKind(), e.getEntryKind(), e.getPath().removeFirstSegments(1), e.getInclusionPatterns(),
							e.getExclusionPatterns(), e.getSourceAttachmentPath(), e.getSourceAttachmentRootPath(), null, e.isExported(), e.getAccessRules(),
							e.combineAccessRules(), e.getExtraAttributes());
				}
			}
			newProject.setRawClasspath(entries, null);
		} catch (final JavaModelException e) {
			UIPlugin.getDefault().logError(e);
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
		return sourcePaths;
	}

	/**
	 * Creates all parent folders of the parent folder
	 *
	 * @param parent The folder containing the library
	 */
	private void createLibFolder(IContainer parent) {
		if (!parent.exists() && (parent instanceof IFolder)) {
			createLibFolder(parent.getParent());
			try {
				((IFolder) parent).create(true, true, null);
			} catch (final CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
		}
	}

	/**
	 * @param description
	 * @param iProjectDescription
	 * @return
	 * @throws CoreException
	 */
	private void setDescription(IProject newProject) throws CoreException {
		final IProject project = builder.featureProject.getProject();
		final IProjectDescription newDescription = newProject.getDescription();
		final IProjectDescription oldDescription = project.getDescription();

		// remove FeatureIDE build commands
		final ICommand[] buildSpec = oldDescription.getBuildSpec();
		final ICommand[] commands = new ICommand[buildSpec.length - 1];
		int i = 0;
		for (final ICommand c : buildSpec) {
			if (ExtensibleFeatureProjectBuilder.BUILDER_ID.equals(c.getBuilderName())) {
				continue;
			}
			commands[i] = c;
			i++;
		}
		newDescription.setBuildSpec(commands);

		// remove the FeatureIDE nature
		final String[] natureIDs = oldDescription.getNatureIds();
		final String[] natures = new String[natureIDs.length - 1];
		int j = 0;
		for (final String id : natureIDs) {
			if (FeatureProjectNature.NATURE_ID.equals(id)) {
				continue;
			}
			natures[j] = id;
			j++;
		}
		newDescription.setNatureIds(natures);

		newProject.setDescription(newDescription, null);
	}

}
