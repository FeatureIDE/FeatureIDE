/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
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
@SuppressWarnings("restriction")
public class Generator extends Job implements IConfigurationBuilderBasics {
	
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
	private int nr;

	@CheckForNull
	private Compiler compiler;

	private BuilderConfiguration configuration;

	 /**
	  * 
	  * @param nr The number of the job
	  * @param builder The {@link ConfigurationBuilder} containing the {@link Generator}
	  */
	public Generator(int nr, ConfigurationBuilder builder) {
		super(nr == 0 ? "Generator" : "Genarator nr. " + nr);
		this.nr = nr;
		this.builder = builder;
		
		if (!builder.createNewProjects) {
			compiler = new Compiler(nr , this);
		}
	}
	
	/**
	 * Generates the configurations of CongfigurationBuilder.configurations
	 * @param monitor
	 */
	@Override
	protected IStatus run(IProgressMonitor monitor) {
		try {
			monitor.setTaskName("Generate products");
			while (true) {
				synchronized (this) {
					if (builder.cancelGeneratorJobs || monitor.isCanceled()) {
						builder.generatorJobs.remove(this);
						return Status.OK_STATUS;
					}
					if (builder.sorter.getBufferSize() == 0) {
						monitor.subTask("(Waiting)");
						while (builder.sorter.getBufferSize() == 0) {
							/** the job waits for a new configuration to build **/
							try {
								// TODO this should be done with wait() and notify()
								wait(1000);
								if ((builder.sorter.getBufferSize() == 0 && builder.finish) || 
										builder.cancelGeneratorJobs) {
									return Status.OK_STATUS;
								}
							} catch (InterruptedException e) {
								UIPlugin.getDefault().logError(e);
							}
						}
					}
				}
				monitor.subTask("(Build)");
				configuration = builder.getConfiguration();
				if (configuration == null) {
					continue;
				}
				
				String name = configuration.getName();
				switch (builder.buildType) {
				case ALL_CURRENT:
					if (builder.createNewProjects) {
						buildConfiguration(builder.featureProject.getProjectName() + SEPARATOR_CONFIGURATION + name, configuration);
					} else {
						builder.featureProject.getComposer().buildConfiguration(builder.folder.getFolder(name), 
								configuration, name);
					}
					break;
				case ALL_VALID:
					if (builder.createNewProjects) {
						buildConfiguration(builder.featureProject.getProjectName() + SEPARATOR_VARIANT + name, configuration);
					} else {
						builder.featureProject.getComposer().buildConfiguration(builder.folder.getFolder(CONFIGURATION_NAME + name), 
								configuration, CONFIGURATION_NAME + name);
					}
					break;
				case T_WISE:
					if (builder.createNewProjects) {
						buildConfiguration(builder.featureProject.getProjectName() + SEPARATOR_T_WISE + name, configuration);
					} else {
						builder.featureProject.getComposer().buildConfiguration(builder.folder.getFolder(name), 
								configuration, name);
					}
					break;

				}
				if (compiler != null) {
					monitor.subTask("(Compile)");
					compiler.compile(configuration);
				}
				
				builder.builtConfigurations++;
			}
		} catch (Exception e) {
			UIPlugin.getDefault().logError("Error in configuration " + configuration, e);
			/**
			 * If there is any build error the configuration will be built again.
			 * And because this job is terminated a new one will be created.
			 */
			UIPlugin.getDefault().logWarning("The Generator nr. " + nr + " will be restarted.");
			builder.createNewGenerator(nr);
		} finally {
			builder.generatorJobs.remove(this);
			monitor.done();
		}
		return Status.OK_STATUS;
	}

	/**
	 * Builds the configuration in a new project with the given name.
	 * @param name The name of the new project
	 */
	void buildConfiguration(String name, Configuration configuration) {
		IPath p2 = new Path("/" + name);
		ConfigurationProject project = new ConfigurationProject(p2, (Workspace) builder.featureProject.getProject().getWorkspace());
		try {
			if (!project.exists()) { 
				project.create(null);
			}
			project.open(null);
			setDescription(project);
		} catch (CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
		try {
			if (project.hasNature(JAVA_NATURE)) {
				setClassPath(project);
			}
		} catch (CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
			
		final IComposerExtensionClass composer = builder.featureProject.getComposer();
		final IFolder sourceFolder = project.getFolder("src");
		composer.buildConfiguration(sourceFolder, configuration, name);
		if (composer instanceof PPComposerExtensionClass) {
			((PPComposerExtensionClass)composer).postProcess(sourceFolder);
		}
			
		try {
			IFile modelFile = builder.featureProject.getModelFile();
			modelFile.copy(project.getFile(modelFile.getName()).getFullPath(), true, null);
			project.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * Sets the classpath entries for the newly created project
	 * @param p The new project
	 */
	// TODO remove redundant calculations for each configuration
	// TODO copy settings
	private void setClassPath(IProject p) {
		JavaProject baseProject = new JavaProject(builder.featureProject.getProject(), null);
		JavaProject newProject = new JavaProject(p, null);
		try {
			IClasspathEntry[] entries = baseProject.getRawClasspath().clone();
			for (int i = 0;i < entries.length;i++) {
				// set source entry to "src"
				IClasspathEntry e = entries[i];
				if (entries[i].getEntryKind() == IClasspathEntry.CPE_SOURCE) {
					entries[i] = new ClasspathEntry(e.getContentKind(), e.getEntryKind(), 
								new Path("src"), e.getInclusionPatterns(), e.getExclusionPatterns(), 
								e.getSourceAttachmentPath(), e.getSourceAttachmentRootPath(), null, 
								e.isExported(), e.getAccessRules(), e.combineAccessRules(), e.getExtraAttributes());
				} else if (e.getEntryKind() == IClasspathEntry.CPE_LIBRARY){
					// set the library entries and copy the libraries 
					// which are direct at the old projects folder  
					IPath path = e.getPath().removeFirstSegments(1);
					IProject project = builder.featureProject.getProject();
					IFile file = project.getFile(path);
					if (!file.exists()) {
						path = e.getPath();
						file = project.getFile(path);
						if (!file.exists()) {
							continue;
						}
					}
					createLibFolder(p.getFile(path).getParent());
					IFile destination = p.getFile(e.getPath().removeFirstSegments(1));
					if (!destination.exists()) {
						file.copy(destination.getFullPath(), true, null);
					}
					entries[i] = new ClasspathEntry(e.getContentKind(), e.getEntryKind(), 
							e.getPath().removeFirstSegments(1), e.getInclusionPatterns(), e.getExclusionPatterns(), 
							e.getSourceAttachmentPath(), e.getSourceAttachmentRootPath(), null, 
							e.isExported(), e.getAccessRules(), e.combineAccessRules(), e.getExtraAttributes());
				}
			}
			newProject.setRawClasspath(entries, null);
		} catch (JavaModelException e) {
			UIPlugin.getDefault().logError(e);
		} catch (CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * Creates all parent folders of the parent folder
	 * @param parent The folder containing the library
	 */
	private void createLibFolder(IContainer parent) {
		if (!parent.exists() && parent instanceof IFolder) {
			createLibFolder(parent.getParent());
			try {
				((IFolder)parent).create(true, true, null);
			} catch (CoreException e) {
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
		IProject project = builder.featureProject.getProject();
		IProjectDescription newDescription = newProject.getDescription();
		IProjectDescription oldDescription = project.getDescription();
		
		// remove FeatureIDE build commands
		ICommand[] buildSpec = oldDescription.getBuildSpec();
		ICommand[] commands = new ICommand[buildSpec.length - 1];
		int i = 0;
		for (ICommand c : buildSpec) {
			if (ExtensibleFeatureProjectBuilder.BUILDER_ID.equals(c.getBuilderName())) {
				continue;
			}
			commands[i] = c;
			i++;
		}
		newDescription.setBuildSpec(commands);
		
		// remove the FeatureIDE nature
		String[] natureIDs = oldDescription.getNatureIds();
		String[] natures = new String[natureIDs.length - 1];
		int j = 0;
		for (String id : natureIDs) {
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
