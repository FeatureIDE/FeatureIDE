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
package de.ovgu.featureide.core.mpl;

import static de.ovgu.featureide.fm.core.localization.StringTable.EMPTY___;
import static de.ovgu.featureide.fm.core.localization.StringTable.INTERFACES;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IncrementalProjectBuilder;
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
import de.ovgu.featureide.core.mpl.job.CreateInterfaceJob;
import de.ovgu.featureide.core.mpl.job.PrintFeatureInterfacesJob;
import de.ovgu.featureide.fm.core.AbstractCorePlugin;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

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
	}

	@Override
	public void stop(BundleContext context) throws Exception {
		super.stop(context);
		plugin = null;
	}

	public void addMSPLNature(IFeatureProject curFeatureProject) {
		final IProject project = curFeatureProject.getProject();
		try {
			final IProjectDescription description = project.getDescription();
			final String[] natures = description.getNatureIds();
			final String[] newNatures = new String[natures.length + 1];
			System.arraycopy(natures, 0, newNatures, 0, natures.length);
			newNatures[natures.length] = MSPLNature.NATURE_ID;
			description.setNatureIds(newNatures);
			project.setDescription(description, null);

			// create directories for MPL
			final IFolder mplFolder = project.getFolder(INTERFACES);
			if (!mplFolder.exists()) {
				mplFolder.create(true, true, null);
			}

			final IFolder importFolder = project.getFolder("MPL");
			if (!importFolder.exists()) {
				importFolder.create(true, true, null);
			}

			final IFolder mappingFolder = project.getFolder("InterfaceMapping");
			if (!mappingFolder.exists()) {
				mappingFolder.create(true, true, null);
			}

			final IFile mappingFile = mappingFolder.getFile("default.config");
			if (!mappingFile.exists()) {
				mappingFile.create(new ByteArrayInputStream(new byte[0]), true, null);
			}
			project.setPersistentProperty(mappingConfigID, "default.config");

			// create interfaces mapping file
			final IFile mplVelvet = project.getFile("mpl.velvet");
			if (!mplVelvet.exists()) {
				// IFile.create() needs an source
				final byte[] bytes = ("concept " + project.getName() + " : " + project.getName()).getBytes();
				final InputStream source = new ByteArrayInputStream(bytes);
				mplVelvet.create(source, true, null);
			}
		} catch (final CoreException e) {
			logError(e);
		}
	}

	public void addInterfaceNature(IFeatureProject curFeatureProject) {
		// TODO MPL: workaround: only for feature house projects
		if ("de.ovgu.featureide.composer.featurehouse".equals(curFeatureProject.getComposerID())) {
			try {
				final IProjectDescription description = curFeatureProject.getProject().getDescription();
				final String[] natures = description.getNatureIds();
				final String[] newNatures = new String[natures.length + 1];
				System.arraycopy(natures, 0, newNatures, 0, natures.length);
				newNatures[natures.length] = InterfaceProjectNature.NATURE_ID;
				description.setNatureIds(newNatures);
				curFeatureProject.getProject().setDescription(description, null);
			} catch (final CoreException e) {
				logError(e);
			}
		}
	}

	public void removeInterfaceNature(IProject project) {
		try {
			final IProjectDescription description = project.getDescription();
			final String[] natures = description.getNatureIds();
			final String[] newNatures = new String[natures.length - 1];
			int i = 0;
			for (final String nature : natures) {
				if (!nature.equals(InterfaceProjectNature.NATURE_ID)) {
					newNatures[i++] = nature;
				}
			}
			description.setNatureIds(newNatures);
			project.setDescription(description, null);
		} catch (final CoreException e) {
			logError(e);
		}
	}

	public InterfaceProject addProject(IProject project) {
		IFeatureProject curFeatureProject = null;
		try {
			if (project.hasNature(FeatureProjectNature.NATURE_ID)) {
				curFeatureProject = CorePlugin.getFeatureProject(project);
			}
			if (curFeatureProject == null) {
				for (final IFeatureProject fp : CorePlugin.getFeatureProjects()) {
					if (constructInterfaceProjectName(fp.getProjectName()).equals(project.getName())) {
						curFeatureProject = fp;
						break;
					}
				}
			}
		} catch (final CoreException e) {
			logError(e);
		}
		final InterfaceProject interfaceProject = new InterfaceProject(project, curFeatureProject);

		projectMap.put(project.getName(), interfaceProject);
		interfaceProject.getFeatureModel().addListener(new IEventListener() {

			@Override
			public void propertyChange(FeatureIDEEvent evt) {
				if (EventType.MODEL_DATA_CHANGED == evt.getEventType()) {
//					interfaceProject.loadSignatures(true);
				} else if (EventType.MODEL_LAYOUT_CHANGED == evt.getEventType()) {
//					interfaceProject.loadSignatures(true);
				}
			}
		});
		return interfaceProject;
	}

	public InterfaceProject getInterfaceProject(String projectName) {
		InterfaceProject interfaceProject = projectMap.get(projectName);
		if (interfaceProject == null) {
			final IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
			if (isInterfaceProject(project)) {
				interfaceProject = addProject(project);
			}
		}
		return interfaceProject;
	}

	public InterfaceProject getInterfaceProject(IProject project) {
		InterfaceProject interfaceProject = projectMap.get(project.getName());
		if ((interfaceProject == null) && isInterfaceProject(project)) {
			interfaceProject = addProject(project);
		}
		return interfaceProject;
	}

	public boolean isInterfaceProject(IProject project) {
		try {
			return project.isAccessible() && project.hasNature(InterfaceProjectNature.NATURE_ID);
		} catch (final CoreException e) {
			logError(e);
			return false;
		}
	}

	private static String constructInterfaceProjectName(String featureProjektName) {
		return EMPTY___ + featureProjektName + "_Interfaces";
	}

	public void setupMultiFeatureProject(Collection<IFeatureProject> featureProjects) {
		for (final IFeatureProject featureProject : featureProjects) {
			final String projectName = constructInterfaceProjectName(featureProject.getProjectName());

			final IProject newProject = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
			final IProjectDescription description = ResourcesPlugin.getWorkspace().newProjectDescription(projectName);
			description.setNatureIds(new String[] { InterfaceProjectNature.NATURE_ID });
			try {
				newProject.create(description, null);
				newProject.open(null);

				newProject.getFile(new Path("model.xml")).create(featureProject.getModelFile().getContents(), true, null);

				final InputStream stream = new ByteArrayInputStream("".getBytes());
				newProject.getFile(new Path("configuration.config")).create(stream, true, null);
				newProject.getFile(new Path(".xconf")).create(stream, true, null);
				stream.close();

				final InterfaceProject interfaceProject = new InterfaceProject(newProject, featureProject);
				projectMap.put(projectName, interfaceProject);
			} catch (final Exception e) {
				logError(e);
			}
		}
	}

//	public void buildJavaProject(IFile featureListFile, String name) {
//		new JavaProjectWriter(getInterfaceProject(featureListFile.getProject())).buildJavaProject(featureListFile, name);
//	}

	public void setCurrentMapping(IProject project, String name) {
		try {
			project.setPersistentProperty(mappingConfigID, name);
		} catch (final CoreException e) {
			logError(e);
		}
	}

	public void addViewTag(IProject project, String name) {
		final InterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
//			interfaceProject.getRoleMap().addDefaultViewTag(name);
//			refresh(interfaceProject);
		}
	}

	public void scaleUpViewTag(IProject project, String name, int level) {
		final InterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
//			interfaceProject.scaleUpViewTag(name, level);
//			refresh(interfaceProject);
		}
	}

	public void deleteViewTag(IProject project, String name) {
		final InterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
//			interfaceProject.removeViewTag(name);
//			refresh(interfaceProject);
		}
	}

	public void refresh(IProject project) {
		final InterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
//			interfaceProject.loadSignatures(true);
			try {
				project.build(IncrementalProjectBuilder.FULL_BUILD, null);
			} catch (final CoreException e) {
				logError(e);
			}

		}
	}

	public void buildFeatureInterfaces(LinkedList<IProject> projects, String folder, String viewName, int viewLevel, int configLimit) {
		final ArrayList<JobArguments> arguments = new ArrayList<>(projects.size());
		for (final IProject iProject : projects) {
			arguments.add(new PrintFeatureInterfacesJob.Arguments(folder, iProject));
		}
		FMCorePlugin.getDefault().startJobs(arguments, true);
	}

	public void buildConfigurationInterfaces(LinkedList<IProject> projects, String viewName, int viewLevel, int configLimit) {
//		ArrayList<JobArguments> arguments = new ArrayList<>(projects.size());
//		for (IProject iProject : projects) {
//			arguments.add(new PrintComparedInterfacesJob.Arguments(iProject));
//		}
//		FMCorePlugin.getDefault().startJobs(arguments, true);
	}

	public void compareConfigurationInterfaces(LinkedList<IProject> projects, String viewName, int viewLevel, int configLimit) {
//		ArrayList<JobArguments> arguments = new ArrayList<>(projects.size());
//		for (IProject iProject : projects) {
//			arguments.add(new PrintComparedInterfacesJob.Arguments(iProject));
//		}
//		FMCorePlugin.getDefault().startJobs(arguments, true);
	}

	public void buildExtendedModules(LinkedList<IProject> projects, String folder) {
//		ArrayList<JobArguments> arguments = new ArrayList<>(projects.size());
//		for (IProject iProject : projects) {
//			arguments.add(new PrintExtendedSignaturesJob.Arguments(folder, iProject));
//		}
//		FMCorePlugin.getDefault().startJobs(arguments, true);
	}

	public void printStatistics(LinkedList<IProject> projects, String folder) {
//		ArrayList<JobArguments> arguments = new ArrayList<>(projects.size());
//		for (IProject iProject : projects) {
//			arguments.add(new PrintStatisticsJob.Arguments(folder, iProject));
//		}
//		FMCorePlugin.getDefault().startJobs(arguments, true);
	}

	public void createInterface(IProject mplProject, IFeatureProject featureProject, Collection<String> featureNames) {
		final ArrayList<JobArguments> arguments = new ArrayList<>(1);
		arguments.add(new CreateInterfaceJob.Arguments(featureProject.getProjectName(), featureProject.getFeatureModel(), featureNames));
		FMCorePlugin.getDefault().startJobs(arguments, true);
	}

}
