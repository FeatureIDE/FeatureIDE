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
package de.ovgu.featureide.ui.actions.generator;

import java.util.LinkedList;

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
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * This {@link Job} builds all configurations of the corresponding {@link ConfigurationBuilder}
 * 
 * @author Jens Meinicke
 */
@SuppressWarnings("restriction")
public class Generator extends Job implements IConfigurationBuilderBasics {
	
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
	
	LinkedList<BuilderConfiguration> configurations = new LinkedList<BuilderConfiguration>();

	private BuilderConfiguration c;

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
			compiler.setPriority(Job.LONG);
			compiler.schedule();
		}
	}
	
	/**
	 * Generates the configurations of CongfigurationBuilder.configurations
	 * @param monitor
	 */
	@Override
	protected IStatus run(IProgressMonitor monitor) {
		try {
			while (true) {
				synchronized (this) {
					if (builder.cancelGeneratorJobs || monitor.isCanceled()) {
						if (compiler != null) {
							compiler.finish();
						}
						builder.generatorJobs.remove(this);
						return Status.OK_STATUS;
					}
					if (builder.configurations.isEmpty()) {
						monitor.setTaskName(generated + " produrcts generated. (Waiting)");
						while (builder.configurations.isEmpty()) {
							/** the job waits for a new configuration to build **/
							try {
								// TODO this should be done with wait() and notify()
								wait(1000);
								if ((builder.configurations.isEmpty() && builder.finish) || 
										builder.cancelGeneratorJobs) {
									builder.generatorJobs.remove(this);
									if (compiler != null) {
										compiler.finish();
									}
									return Status.OK_STATUS;
								}
							} catch (InterruptedException e) {
								UIPlugin.getDefault().logError(e);
							}
						}
					}
				}
				c = builder.getConfiguration();
				if (c == null) {
					continue;
				}
				monitor.setTaskName(generated + " produrcts generated. (Running)");
				String name = c.getName();
				if (builder.buildAllValidConfigurations) {
					if (builder.createNewProjects) {
						buildConfiguration(builder.featureProject.getProjectName() + SEPARATOR_VARIANT + name, c);
					} else {
						builder.featureProject.getComposer().buildConfiguration(builder.folder.getFolder(CONFIGURATION_NAME + name), 
								c, CONFIGURATION_NAME + name);
					}

				} else {
					if (builder.createNewProjects) {
						buildConfiguration(builder.featureProject.getProjectName() + SEPARATOR_CONFIGURATION + name, c);
					} else {
						builder.featureProject.getComposer().buildConfiguration(builder.folder.getFolder(name), 
								c, name);
					}
				}
				
				addConfiguration(c);
				builder.builtConfigurations++;

				monitor.setTaskName(++generated + " produrcts generated. (Running)");
			}
		} catch (Exception e) {
			UIPlugin.getDefault().logError("The Generator nr. " + nr + " will be restarted.", e);
			/**
			 * If there is any build error the configuration will be built again.
			 * And because this job is terminated a new one will be created.
			 */
			if (compiler != null) {
				compiler.finish();
				try {
					compiler.join();
				} catch (InterruptedException e1) {
					UIPlugin.getDefault().logError(e);
				}
			}
			builder.generatorJobs.remove(this);
			builder.createNewGenerator(nr);
			builder.addConfiguration(c);
		}
		return Status.OK_STATUS;
	}

	@CheckForNull
	public BuilderConfiguration getConfiguration() {
		if (configurations.isEmpty()) {
			return null;
		}
		BuilderConfiguration c = configurations.getFirst();
		configurations.remove();
		return c;
	}
	
	public void addConfiguration(BuilderConfiguration c) {
		configurations.add(c);
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
		
		setClassPath(project);
			
		builder.featureProject.getComposer().buildConfiguration(project.getFolder("src"), configuration, name);
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
					file.copy(p.getFile(e.getPath().removeFirstSegments(1)).getFullPath(), true, null);
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
