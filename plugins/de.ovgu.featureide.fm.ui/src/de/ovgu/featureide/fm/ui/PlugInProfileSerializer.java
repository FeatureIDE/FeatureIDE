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
package de.ovgu.featureide.fm.ui;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.internal.ui.packageview.PackageFragmentRootContainer;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.ISelectionService;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.internal.Workbench;

import de.ovgu.featureide.fm.core.ProfileManager;
import de.ovgu.featureide.fm.core.ProfileManager.Color;
import de.ovgu.featureide.fm.core.ProfileManager.GroupedProperties;
import de.ovgu.featureide.fm.core.ProfileManager.Project;
import de.ovgu.featureide.fm.core.ProfileManager.Project.Profile;
import de.ovgu.featureide.fm.core.ProfileManager.Project.ProfileSerializer;
import de.ovgu.featureide.fm.core.ProfileManager.Project.ProjectSerializer;

/**
 * TODO description
 * 
 * @author marcus
 */
public class PlugInProfileSerializer {

	public static final ProjectSerializer FEATURE_PROJECT_SERIALIZER = new ProjectSerializer() {

		@Override
		public boolean hasProject(String projectName) {
			try {
				Project result = getProject(projectName);
				return result != null;
			} catch (Exception e) {
				return false;
			}
		}

		@Override
		public Collection<Project> getProjects() {
			ArrayList<Project> retval = new ArrayList<>();
			for (IProject project : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
				retval.add(getProject(project.getName()));
			}
			return retval;
		}

		@Override
		public Project getProject(String projectName) {
			for (IProject projects : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
				final String projectPath = projects.getLocation().toFile().getAbsolutePath();
				if (projectPath.equals(projectName) && projects.isOpen())
					return new Project(projectName, FEATURE_PROJECT_PROFILE_SERIALIZER);
			}
			throw new NoSuchElementException(projectName);

			//			IProject eclipseProject = getCurrentIProject();
			//			if (eclipseProject.getName().equals(projectName)) {
			//				return new Project(projectName, FEATURE_PROJECT_PROFILE_SERIALIZER);
			//			}
			//			throw new NoSuchElementException("No current project called \"" + projectName + "\"");
		}

		//		IProject getCurrentIProject() {
		////			for(IProject projects : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
		////				System.out.println("Project..." + projects.getName());
		////				System.out.println("Open? : "  + projects.isOpen());
		////			}
		////			ISelection selection = getSite().getWorkbenchWindow().getSelectionService();
		////			
		////			if (selection instanceof IStructuredSelection) {
		////		        IStructuredSelection ssel = (IStructuredSelection) selection;
		////		        Object obj = ssel.getFirstElement();
		////		        IFile file = (IFile) Platform.getAdapterManager().getAdapter(obj,
		////		                IFile.class);
		////		        if (file == null) {
		////		            if (obj instanceof IAdaptable) {
		////		                file = (IFile) ((IAdaptable) obj).getAdapter(IFile.class);
		////		            }
		////		        }
		////		        if (file != null) {
		////		            // do something
		////		        }
		//		    }
		//			
		//			
		//			IProject project = ResourcesPlugin.getWorkspace().
		//			if (project == null)
		//				throw new NoSuchElementException("No current project");
		//			else return project;
		//		}

		@Override
		public String getCurrentProject() {
			//			IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
			//			if (window != null) {
			//				IStructuredSelection selection = (IStructuredSelection) window.getSelectionService().getSelection();
			//				Object firstElement = selection.getFirstElement();
			//				if (firstElement instanceof IAdaptable) {
			//					IProject project = (IProject) ((IAdaptable) firstElement).getAdapter(IProject.class);
			//					return project.getName();
			//				}
			//			}
			throw new IllegalStateException();
		}
	};

	public static final ProfileSerializer FEATURE_PROJECT_PROFILE_SERIALIZER = new ProfileSerializer() {

		public static final String EXCEPTION_NO_PROFILE = "The profile \"%s\" can not be located in project folder \"%s\"";

		@Override
		public boolean writeProfile(Project project, Profile profile) {
			System.out.println("Write profile..." + profile);
			final IProject eclipseProject = getEclipseProjectOf(project.getName());
			if (!eclipseProject.getFolder(".profiles").exists()) {
				createProfilesFolder(eclipseProject);
			}
			GroupedProperties properties = new GroupedProperties();
			final List<String> features = profile.getFeatures();
			properties.setProperty("name", profile.getName());
			properties.setProperty("coloring.number-of-features", String.valueOf(features.size()));
			properties.setProperty("active", profile.isActiveProfile() ? "yes" : "no");
			for (int i = 0; i < features.size(); i++) {
				final String featureName = features.get(i);
				final String groupName = "coloring.feature" + i;
				properties.setProperty(groupName, "display-name", featureName);
				properties.setProperty(groupName, "color", profile.getColor(featureName).toString());
			}

			IFolder profileFileFolder = eclipseProject.getFolder(".profiles");
			final IFile profileOutputFile = profileFileFolder.getFile(profile.getName() + ".profile");
			try (FileOutputStream fos = new FileOutputStream(profileOutputFile.getRawLocation().toFile())) {
				properties.store(fos, "FeatureIDE profile file");
				fos.close();
				return true;
			} catch (Exception e) {
				e.printStackTrace();
				return false;
			}
		}

		private InputStream getContentsOfIFile(IFile file) throws FileNotFoundException {
			return new FileInputStream(file.getRawLocation().toFile());
		}

		private void createProfilesFolder(IProject eclipseProject) {
			IFolder profileFileFolder = eclipseProject.getFolder(".profiles");
			try {
				profileFileFolder.create(false, true, null);
			} catch (CoreException e) {
				e.printStackTrace();
			}
		}

		@Override
		public boolean removeProfile(Project project, Profile profile) {
			if (!hasProfile(project, profile.getName()))
				return false;
			final IProject eclipseProject = getEclipseProjectOf(project.getName());
			IFolder profileFileFolder = eclipseProject.getFolder(".profiles");

			try {
				for (IResource res : profileFileFolder.members()) {
					if (res instanceof IFile) {
						if (res.getName().endsWith(".profile") && res.getName().equals(profile.getName() + ".profile")) {
							final IFile profileFile = profileFileFolder.getFile(res.getName());
							profileFile.delete(true, new NullProgressMonitor());
							return true;
						}
					}
				}
			} catch (Exception e) {
				e.printStackTrace();
			}

			return false;
		}

		//	Map<String, List<IFile>> projectColorProfileFiles = new HashMap<>();

		//		IProject getCurrentIProject() {
		//			IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		//			if (window != null) {
		//				IStructuredSelection selection = (IStructuredSelection) window.getSelectionService().getSelection();
		//				Object firstElement = selection.getFirstElement();
		//				if (firstElement instanceof IAdaptable) {
		//					IProject project = (IProject) ((IAdaptable) firstElement).getAdapter(IProject.class);
		//					return project;
		//				}
		//			}
		//			throw new NoSuchElementException("No current project");
		//		}

		@Override
		public Collection<Profile> readProfiles(Project project) {
			ArrayList<Profile> retval = new ArrayList<>();

			final IProject eclipseProject = getEclipseProjectOf(project.getName());

			IFolder profileFileFolder = eclipseProject.getFolder(".profiles");
			if (!eclipseProject.getFolder(".profiles").exists()) {
				return retval;
				//				IProgressMonitor progressMonitor = new NullProgressMonitor();
				//				try {
				//					eclipseProject.create(progressMonitor);
				//					eclipseProject.open(progressMonitor);
				//					profileFileFolder.create(true, true, progressMonitor);
				//				} catch (CoreException e) {
				//					e.printStackTrace();
				//				}
			} else {

				try {
					profileFileFolder.refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());
					for (IResource res : profileFileFolder.members()) {
						if (res instanceof IFile) {
							if (res.getName().endsWith(".profile")) {
								final IFile profileFile = eclipseProject.getFolder(".profiles").getFile(res.getName());
								//								if (!projectColorProfileFiles.containsKey(project.getName())) {
								//									projectColorProfileFiles.put(project.getName(), new ArrayList<IFile>());
								//								}
								//								Profile profile = readProfiles(project.getName());
								//								projectColorProfileFiles.get(project.getName()).add(profileFile);
								try (InputStream fis = getContentsOfIFile(profileFile)) {
									GroupedProperties properties = new GroupedProperties();
									properties.load(fis);
									fis.close();
									//System.out.println(profileFile.getFullPath());
									retval.add(readProfile(project, properties.getProperty("name")));
								} catch (Exception e) {
									e.printStackTrace();
								}
							}
						}
					}
				} catch (Exception e) {
					e.printStackTrace();
				}
			}

			return retval;
		}

		private IProject getEclipseProjectOf(String eclipseProjectPath) {
			for (IProject projects : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
				if (projects.getLocation().toFile().getAbsolutePath().equals(eclipseProjectPath) && projects.isOpen())
					return projects;
			}
			throw new NoSuchElementException(eclipseProjectPath);
		}

		@Override
		public Profile readProfile(Project project, String profileName) {
			//if (!hasProfile(project, profileName))
			//	throw new NoSuchElementException(String.format(EXCEPTION_NO_PROFILE, profileName, project));
			//else {
			GroupedProperties properties = loadProperties(project, profileName);
			Profile retval = new Profile(profileName, project);
			int numberOfFeatures = Integer.valueOf(properties.getProperty("coloring.number-of-features", "0"));
			final boolean isActive = ((String) properties.getProperty("active", "no")).equals("yes");
			if (isActive)
				retval.internalSetAsActiveProfile();
			for (int i = 0; i < numberOfFeatures; i++) {
				final String groupName = "coloring.feature" + i;
				final String featureName = properties.getProperty(groupName, "display-name", "Unkown Feature Name");
				final Color featureColor = Color.valueOf((String) properties.getProperty(groupName, "color", Color.NO_COLOR.name()));
				retval.setFeatureColor(featureName, featureColor);
			}
			return retval;
			//}
		}

		private GroupedProperties loadProperties(Project project, String profileName) {
			GroupedProperties properties = new GroupedProperties();
			IFolder profileFileFolder = getEclipseProjectOf(project.getName()).getFolder(".profiles");
			try {
				for (IResource resource : profileFileFolder.members()) {
					if (resource.getFileExtension().equals("profile")) {
						try (InputStream fis = getContentsOfIFile(profileFileFolder.getFile(resource.getName()))) {
							properties.load(fis);
							fis.close();
							if (properties.getProperty("name").equals(profileName)) {
								return properties;
							}
						} catch (Exception e) {
							e.printStackTrace();
						}
					}
				}
				throw new NoSuchElementException();
			} catch (CoreException e) {
				e.printStackTrace();
				throw new NoSuchElementException();
			}
		}

		@Override
		public boolean hasProfiles(Project project) {
			return !readProfiles(project).isEmpty();
		}

		@Override
		public boolean hasProfile(Project project, String profileName) {
			GroupedProperties properties = new GroupedProperties();
			IFolder profileFileFolder = getEclipseProjectOf(project.getName()).getFolder(".profiles");
			try {
				for (IResource resource : profileFileFolder.members()) {
					if (resource.getFileExtension().equals("profile")) {
						try (InputStream fis = getContentsOfIFile(profileFileFolder.getFile(resource.getName()))) {
							properties.load(fis);
							fis.close();
							if (properties.getProperty("name").equals(profileName)) {
								return true;
							}
						} catch (Exception e) {
							e.printStackTrace();
						}
					}
				}
				return false;
			} catch (CoreException e) {
				e.printStackTrace();
				return false;
			}
		}
	};

}
