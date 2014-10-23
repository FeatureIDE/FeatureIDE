/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.mpl;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.QualifiedName;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.FeatureProjectNature;
import de.ovgu.featureide.core.mpl.builder.InterfaceProjectNature;
import de.ovgu.featureide.core.mpl.builder.MSPLNature;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.core.mpl.io.writer.JavaProjectWriter;
import de.ovgu.featureide.core.mpl.job.CreateFujiSignaturesJob;
import de.ovgu.featureide.core.mpl.job.CreateInterfaceJob;
import de.ovgu.featureide.core.mpl.job.JobManager;
import de.ovgu.featureide.core.mpl.job.PrintComparedInterfacesJob;
import de.ovgu.featureide.core.mpl.job.PrintDocumentationJob;
import de.ovgu.featureide.core.mpl.job.PrintDocumentationStatisticsJob;
import de.ovgu.featureide.core.mpl.job.PrintExtendedSignaturesJob;
import de.ovgu.featureide.core.mpl.job.PrintFeatureInterfacesJob;
import de.ovgu.featureide.core.mpl.job.PrintStatisticsJob;
import de.ovgu.featureide.core.mpl.job.util.AJobArguments;
import de.ovgu.featureide.core.mpl.job.util.IChainJob;
import de.ovgu.featureide.core.mpl.util.ConfigurationChangeListener;
import de.ovgu.featureide.core.mpl.util.EditorTracker;
import de.ovgu.featureide.fm.core.AbstractCorePlugin;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.PropertyConstants;

/** 
 * Plug-in activator with miscellaneous function for an interface project.
 * 
 * @author Sebastian Krieter
 * @author Reimar Schroeter
 */
public class MPLPlugin extends AbstractCorePlugin {
	public static final String PLUGIN_ID = "de.ovgu.featureide.core.mpl";

	public static final QualifiedName mappingConfigID = new QualifiedName("mplproject.mappings", "currentMapping");

	private static MPLPlugin plugin;
	private final HashMap<String, InterfaceProject> projectMap = new HashMap<String, InterfaceProject>();

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	public static MPLPlugin getDefault() {
		return plugin;
	}

	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		EditorTracker.init(new ConfigurationChangeListener());
	}

	@Override
	public void stop(BundleContext context) throws Exception {
		super.stop(context);
		plugin = null;
		EditorTracker.dispose();
	}
	
	public void addMSPLNature(IProject project) {
		IFeatureProject curFeatureProject = CorePlugin.getFeatureProject(project);
		if (curFeatureProject != null) {
			try {				
				IProjectDescription description = project.getDescription();
				String[] natures = description.getNatureIds();
				String[] newNatures = new String[natures.length + 1];
				System.arraycopy(natures, 0, newNatures, 0, natures.length);
				newNatures[natures.length] = MSPLNature.NATURE_ID;
				description.setNatureIds(newNatures);
				project.setDescription(description, null);

				// create directories for MPL
				IFolder mplFolder = project.getFolder("Interfaces");
				if (!mplFolder.exists())
					mplFolder.create(true, true, null);
				
				IFolder importFolder = project.getFolder("MPL");
				if (!importFolder.exists())
					importFolder.create(true, true, null);
				
				IFolder mappingFolder = project.getFolder("InterfaceMapping");
				if (!mappingFolder.exists())
					mappingFolder.create(true, true, null);
				
				IFile mappingFile = mappingFolder.getFile("default.config");
				if (!mappingFile.exists()) {
					mappingFile.create(new ByteArrayInputStream(new byte[0]), true, null);
				}
				project.setPersistentProperty(mappingConfigID, "default.config");
				
				// create interfaces mapping file
				IFile mplVelvet = project.getFile("mpl.velvet");
				if (!mplVelvet.exists()) {
					// IFile.create() needs an source
					byte[] bytes = ("concept " + project.getName() + " : "
							+ project.getName()).getBytes();
					InputStream source = new ByteArrayInputStream(bytes);
					mplVelvet.create(source, true, null);
				}
			} catch (CoreException e) {
				logError(e);
			}
		}
	}
	
	public void addInterfaceNature(IProject project) {
		IFeatureProject curFeatureProject = CorePlugin.getFeatureProject(project);
		// TODO MPL: workaround: only for feature house projects
		if (curFeatureProject != null
				&& "de.ovgu.featureide.composer.featurehouse"
						.equals(curFeatureProject.getComposerID())) {
			try {
				IProjectDescription description = project.getDescription();
				String[] natures = description.getNatureIds();
				String[] newNatures = new String[natures.length + 1];
				System.arraycopy(natures, 0, newNatures, 0, natures.length);
				newNatures[natures.length] = InterfaceProjectNature.NATURE_ID;
				description.setNatureIds(newNatures);
				project.setDescription(description, null);
			} catch (CoreException e) {
				logError(e);
			}
		}
	}
	
	public void removeInterfaceNature(IProject project) {
		try {
			IProjectDescription description = project.getDescription();
			String[] natures = description.getNatureIds();
			String[] newNatures = new String[natures.length - 1];
			int i = 0;
			for (String nature : natures) {
				if (!nature.equals(InterfaceProjectNature.NATURE_ID)) {
					newNatures[i++] = nature;
				}
			}
			description.setNatureIds(newNatures);
			project.setDescription(description, null);
		} catch (CoreException e) {
			logError(e);
		}
	}
	
	private InterfaceProject addProject(IProject project) {
		IFeatureProject curFeatureProject = null;
		try {
			if (project.hasNature(FeatureProjectNature.NATURE_ID)) {
				curFeatureProject = CorePlugin.getFeatureProject(project);
			} else {
				for (IFeatureProject fp : CorePlugin.getFeatureProjects()) {
					if (constructInterfaceProjectName(fp.getProjectName()).equals(project.getName())) {
						curFeatureProject = fp;
						break;
					}
				}
			}
		} catch (CoreException e) {
			logError(e);
		}
		final InterfaceProject interfaceProject = new InterfaceProject(project, curFeatureProject);
		
		projectMap.put(project.getName(), interfaceProject);
		interfaceProject.getFeatureModel().addListener(new PropertyChangeListener() {
			@Override
			public void propertyChange(PropertyChangeEvent evt) {
				if (PropertyConstants.MODEL_DATA_CHANGED.equals(evt.getPropertyName())) {
//					interfaceProject.loadSignatures(true);
				} else if (PropertyConstants.MODEL_LAYOUT_CHANGED.equals(evt.getPropertyName())) {
//					interfaceProject.loadSignatures(true);
				}
			}
		});
		return interfaceProject;
	}
	
	public InterfaceProject getInterfaceProject(String projectName) {
		InterfaceProject interfaceProject = projectMap.get(projectName);
		if (interfaceProject == null) {
			IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
			if (isInterfaceProject(project)) {
				interfaceProject = addProject(project);
			}
		}
		return interfaceProject;
	}
	
	public InterfaceProject getInterfaceProject(IProject project) {
		InterfaceProject interfaceProject = projectMap.get(project.getName());
		if (interfaceProject == null && isInterfaceProject(project)) {
			interfaceProject = addProject(project);
		}
		return interfaceProject;
	}
	
	public boolean isInterfaceProject(IProject project) {
		try {
			return project.isAccessible() && project.hasNature(InterfaceProjectNature.NATURE_ID);
		} catch (CoreException e) {
			logError(e);
			return false;
		}
	}
	
	private static String constructInterfaceProjectName(String featureProjektName) {
		return "_" + featureProjektName + "_Interfaces";
	}
	
	public void setupMultiFeatureProject(Collection<IFeatureProject> featureProjects) {
		for (IFeatureProject featureProject : featureProjects) {			
			String projectName = constructInterfaceProjectName(featureProject.getProjectName());
			
			IProject newProject = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
			IProjectDescription description = ResourcesPlugin.getWorkspace().newProjectDescription(projectName);
			description.setNatureIds(new String[]{InterfaceProjectNature.NATURE_ID});			
			try {
				newProject.create(description, null);
				newProject.open(null);
				
				newProject.getFile(new Path(IOConstants.FILENAME_MODEL)).create(featureProject.getModelFile().getContents(), true, null);

				InputStream stream = new ByteArrayInputStream("".getBytes());
				newProject.getFile(new Path(IOConstants.FILENAME_CONFIG)).create(stream, true, null);
				newProject.getFile(new Path(IOConstants.FILENAME_EXTCONFIG)).create(stream, true, null);
				stream.close();

				InterfaceProject interfaceProject = new InterfaceProject(newProject, featureProject);
				projectMap.put(projectName, interfaceProject);
			} catch (Exception e) {
				logError(e);
			}
		}
	}
	
	public void buildJavaProject(IFile featureListFile, String name) {
		new JavaProjectWriter(getInterfaceProject(featureListFile.getProject())).buildJavaProject(featureListFile, name);
	}
	
	public void setCurrentMapping(IProject project, String name) {
		try {
			project.setPersistentProperty(mappingConfigID, name);
		} catch (CoreException e) {
			logError(e);
		}
	}
	
	public void addViewTag(IProject project, String name) {
		InterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
//			interfaceProject.getRoleMap().addDefaultViewTag(name);
//			refresh(interfaceProject);
		}
	}
	
	public void scaleUpViewTag(IProject project, String name, int level) {
		InterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
//			interfaceProject.scaleUpViewTag(name, level);
//			refresh(interfaceProject);
		}
	}
	
	public void deleteViewTag(IProject project, String name) {
		InterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
//			interfaceProject.removeViewTag(name);
//			refresh(interfaceProject);
		}
	}
	
	public void refresh(IProject project) {
		InterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
			interfaceProject.loadSignatures(true);
		}
	}
	
	public void buildFeatureInterfaces(LinkedList<IProject> projects, String folder, String viewName, int viewLevel, int configLimit) {
		startJobs(projects, new PrintFeatureInterfacesJob.Arguments(folder));
	}
	
	public void buildDocumentation(LinkedList<IProject> projects, String folder, String options, int mode) {
		FMCorePlugin.getDefault().startJobs(projects, 
				new PrintDocumentationJob.Arguments(folder, null, mode, options.split("\\s+")), true);
	}
	
	public void buildDocumentation(LinkedList<IProject> projects, String folder, String options, int mode, String featurename) {
		FMCorePlugin.getDefault().startJobs(projects, 
				new PrintDocumentationJob.Arguments(folder, featurename, mode, options.split("\\s+")), true);
	}
	
	public void buildDocumentationStatistics(LinkedList<IProject> projects, String folder) {
		startJobs(projects, new PrintDocumentationStatisticsJob.Arguments(folder));
	}
	
	public void buildConfigurationInterfaces(LinkedList<IProject> projects, String viewName, int viewLevel, int configLimit) {
		startJobs(projects, new PrintComparedInterfacesJob.Arguments());
	}
	
	public void compareConfigurationInterfaces(LinkedList<IProject> projects, String viewName, int viewLevel, int configLimit) {
		startJobs(projects, new PrintComparedInterfacesJob.Arguments());
	}
	
	public void buildExtendedModules(LinkedList<IProject> projects, String folder) {
		startJobs(projects, new PrintExtendedSignaturesJob.Arguments(folder));
	}
	
	public void printStatistics(LinkedList<IProject> projects, String folder) {
		startJobs(projects, new PrintStatisticsJob.Arguments(folder));
	}
	
	public void startJobs(LinkedList<IProject> projects, AJobArguments arguments) {
		final Object idObject = new Object();
		for (IProject p : projects) {
			InterfaceProject interfaceProject = getInterfaceProject(p);
			if (interfaceProject != null && interfaceProject.getProjectSignatures() == null) {
				IChainJob job = new CreateFujiSignaturesJob();
				job.setProject(p);
				JobManager.addJob(idObject, job);
			}
			IChainJob job = arguments.createJob();
			job.setProject(p);
			JobManager.addJob(idObject, job);
			
		}
	}
	
	public void createInterface(IProject mplProject, IFeatureProject featureProject, Collection<String> featureNames) {
		LinkedList<IProject> projectList = new LinkedList<IProject>();
		projectList.add(mplProject);
		startJobs(projectList, new CreateInterfaceJob.Arguments(featureProject, featureNames));
	}
}
