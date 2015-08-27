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
package de.ovgu.featureide.fm.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.channels.ReadPendingException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Properties;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.fm.core.ProfileManager.Color;
import de.ovgu.featureide.fm.core.ProfileManager.Project.Profile;
import de.ovgu.featureide.fm.core.ProfileManager.Project.ProfileSerializer;
import de.ovgu.featureide.fm.core.ProfileManager.Project.ProjectSerializer;

/**
 * TODO description
 * 
 * @author marcus
 */
public class ProfileManager {

	public static class GroupedProperties extends Properties {

		public String getProperty(String group, String key, String defaultValue) {
			return getProperty(group + '.' + key);
		}

		public void setProperty(String group, String key, String value) {
			setProperty(group + "." + key, value);
		}
	}

	private static final String EXCEPTION_COLOR_INDEX = "No index for color \"%s\" found";

	public static void main(String[] args) {

		final ProfileSerializer profileSerializer = new ProfileSerializer() {

			Map<String, List<Profile>> store = new HashMap<>();

			@Override
			public boolean writeProfile(Project project, Profile profile) {
				if (!store.containsKey(project))
					store.put(project.getName(), new ArrayList<Profile>());
				if (store.get(project.getName()).contains(profile))
					return false;
				store.get(project.getName()).add(profile);
				//System.out.println("writeProfile " + project.getName() + ", Profile = " + profile.name);
				return true;
			}

			@Override
			public boolean removeProfile(Project project, Profile profile) {
				if (!store.containsKey(project.getName()))
					return false;
				store.get(project.getName()).remove(profile);
				//System.out.println("removeProfile " + project.getName() + ", Profile = " + profile.name);
				return true;
			}

			@Override
			public Collection<Profile> readProfiles(Project project) {
				return store.containsKey(project.getName()) ? store.get(project.getName()) : new ArrayList<ProfileManager.Project.Profile>();
			}

			@Override
			public Profile readProfile(Project project, String profileName) {
				for (Profile p : store.get(project.getName()))
					if (p.getName().equals(profileName))
						return p;
				throw new NoSuchElementException();
			}

			@Override
			public boolean hasProfiles(Project project) {
				return true;
			}

			@Override
			public boolean hasProfile(Project project, String profileName) {
				if (!store.containsKey(project.getName()))
					return false;
				else {
					for (Profile p : store.get(project.getName()))
						if (p.getName().equals(profileName))
							return true;
					return false;
				}
			}
		};

		ProjectSerializer testProjectSerializer = new ProjectSerializer() {

			@Override
			public boolean hasProject(String projectName) {
				return projectName.equals("Klaus") || projectName.equals("Mike");
			}

			@Override
			public Collection<Project> getProjects() {
				Collection<Project> projects = new ArrayList<>();
				projects.add(getProject("Klaus"));
				projects.add(getProject("Mike"));
				return Collections.unmodifiableCollection(projects);
			}

			@Override
			public Project getProject(String projectName) {
				Project project;
				switch (projectName) {
				case "Klaus": {
					project = new Project("Klaus", profileSerializer);
				}
					break;
				case "Mike": {
					project = new Project("Mike", profileSerializer);
				}
					break;
				default:
					throw new NoSuchElementException();
				}
				return project;
			}

			@Override
			public String getCurrentProject() {
				return "Klaus";
			}
		};

		Project project = ProfileManager.getProject("Klaus", testProjectSerializer);
		//System.out.println(project);

		project.addProfile("Marcus");
		Project.Profile profile1 = project.getProfile("Marcus");
		profile1.setFeatureColor("Feature1", Color.BLUE);
		profile1.setFeatureColor("Feature2", Color.DARK_GREEN);
		//System.out.println(project);
		project.removeProfile("Marcus");

		project = ProfileManager.getProject("Mike", testProjectSerializer);
		//System.out.println(project);

		profile1 = project.addProfile("Marcus Extra 1");
		profile1.setFeatureColor("Feature1", Color.BLUE);
		profile1.setFeatureColor("Feature2", Color.DARK_GREEN);
		profile1 = project.addProfile("Marcus Extra 2");
		profile1.setFeatureColor("Feature1", Color.BLUE);
		profile1.setFeatureColor("Feature2", Color.DARK_GREEN);
		//System.out.println(project);
	}

	public enum Color {
		NO_COLOR, RED, ORANGE, YELLOW, DARK_GREEN, LIGHT_GREEN, CYAN, LIGHT_GRAY, BLUE, MAGENTA, PINK
	}
	
	public static int toColorIndex(Color color) {
		switch (color) {
		case RED:
			return 0;
		case ORANGE:
			return 1;
		case YELLOW:
			return 2;
		case DARK_GREEN:
			return 3;
		case LIGHT_GREEN:
			return 4;
		case CYAN:
			return 5;
		case LIGHT_GRAY:
			return 6;
		case BLUE:
			return 7;
		case MAGENTA:
			return 8;
		case PINK:
			return 9;
		default:
			return -1;
		}
	}

	/* 
	 * @author Marcus Pinnecke
	 */
	public static ProfileManager.Color getColorFromID(int id) {
		switch (id) {
		case 0:
			return ProfileManager.Color.RED;
		case 1:
			return ProfileManager.Color.ORANGE;
		case 2:
			return ProfileManager.Color.YELLOW;
		case 3:
			return ProfileManager.Color.DARK_GREEN;
		case 4:
			return ProfileManager.Color.LIGHT_GREEN;
		case 5:
			return ProfileManager.Color.CYAN;
		case 6:
			return ProfileManager.Color.LIGHT_GRAY;
		case 7:
			return ProfileManager.Color.BLUE;
		case 8:
			return ProfileManager.Color.MAGENTA;
		case 9:
			return ProfileManager.Color.PINK;
		case -1:
			return ProfileManager.Color.NO_COLOR;
		default:
			throw new IllegalArgumentException(String.format(EXCEPTION_NO_COLOR_MATCH, id));
		}
	}

	/**
	 * @author Marcus Pinnecke
	 */
	private final static String EXCEPTION_NO_COLOR_MATCH = "Color id %d can not be matched to existing colors.";

	private static Map<String, Project> projects = new HashMap<>();

	private static Project getCurrentProject(ProjectSerializer projectSerializer) {
		return getProject(projectSerializer.getCurrentProject(), projectSerializer);
	}

	public static Project getProject(String projectName, ProjectSerializer projectSerializer) {
		if (!projects.containsKey(projectName)) {
			if (!projectSerializer.hasProject(projectName))
				throw new NoSuchElementException(String.format("Project folder \"%s\" is unkown.", projectName));
			else {
				projects.put(projectName, projectSerializer.getProject(projectName));
			}
		}
		return projects.get(projectName);
	}

	//	private static FeatureProject loadColorProfiles(String projectName) {
	//		// TODO Auto-generated method stub
	//		return null;
	//	}
	//
	//	private static boolean hasColorProfiles(String projectName) {
	//		for (IFeatureProject project : CorePlugin.getFeatureProjects()) {
	//			System.out.println(project.getProject().getFullPath().toString());
	//		}
	//		// TODO Auto-generated method stub
	//		return false;
	//	}

	public static boolean hasProject(String projectName) {
		return projects.containsKey(projectName);
	}

	//public static Collection<Project> getProjects() {
	//	return Collections.unmodifiableCollection(projects.values());
	//}

	//public static Collection<String> getProjectNames() {
	//	return Collections.unmodifiableCollection(projects.keySet());
	//}

	//public static Project getProject(String projectName) {
	//	if (!projects.containsKey(projectName))
	//		throw new NoSuchElementException();
	//	else
	//		return projects.get(projectName);
	//}

	public static class Project {

		public ProfileSerializer profileSerializer;

		@Override
		public String toString() {
//			String s = "";
//			for (Profile profile : profileSerializer.readProfiles(this))
//			 	s += profile + " ";		
			return "FeatureProject [name=" + name + ", profiles=" + "?" + "]";
		}

		public static interface ProjectSerializer {

			public boolean hasProject(String projectName);

			/**
			 * @return
			 */
			public String getCurrentProject();

			public Project getProject(String projectName);

			public Collection<Project> getProjects();

		}

		private static class PrintableMap<K, V> extends HashMap<K, V> {
			@Override
			public String toString() {
				StringBuilder string = new StringBuilder();
				string.append("[");
				final String[] keys = super.keySet().toArray(new String[super.keySet().size()]);
				for (int i = 0; i < keys.length; i++)
					string.append(keys[i] + "=" + super.get(keys[i]) + (i < keys.length - 1 ? ", " : ""));
				string.append("]");
				return string.toString();
			}
		}

		//private PrintableMap<String, Profile> profiles = new PrintableMap<>();

		private String name;

		public String getName() {
			return name;
		}

		/**
		 * @param projectName
		 */
		public Project(String projectName, ProfileSerializer profileSerializer) {
			this.name = projectName;
			this.profileSerializer = profileSerializer;
//			for (Profile profile : profileSerializer.readProfiles(this))
//				profiles.put(profile.name, profile);
//			if (profileSerializer.readProfiles(this).isEmpty()) {
//				addProfile("Default", true);
//			}
		}

		public Profile addProfile(String profileName) {
			checkNameConflict(profileName);
			final Profile profile = new Profile(profileName, this);
			profileSerializer.writeProfile(this, profile);
//			profiles.put(profileName, profile);
			return profile;
		}

		public Profile addProfile(String profileName, boolean setAsActive) {
			Profile profile = addProfile(profileName);
//			if (setAsActive)
//				profile.setAsActiveProfile();
			return profile;
		}

		public boolean removeProfile(String profileName) {
			if (profileSerializer.readProfiles(this).contains(profileName) && !profileName.equals("Default")) {
				Profile p = profileSerializer.readProfile(this, profileName);
				p.delete();
				getProfile("Default").setAsActiveProfile();
//				profiles.remove(profileName);
				return true;
			} else
				return false;
		}

		public Profile getProfile(String profileName) {
			Collection<Profile> profiles = profileSerializer.readProfiles(this);
			for (Profile p : profiles)
				if (p.name.equals(profileName))
					return p;
			
			throw new NoSuchElementException(profileName);
		}

		public Collection<Profile> getProfiles() {
			return Collections.unmodifiableCollection(profileSerializer.readProfiles(this));
		}

		public Collection<String> getProfileNames() {
			Collection<Profile> profiles = getProfiles();
			ArrayList<String> profileNames = new ArrayList<>(profiles.size());
			for (Profile p : profiles)
				profileNames.add(p.name);
			return profileNames;
		}

		public interface ProfileSerializer {

			public Collection<Profile> readProfiles(Project project);

			public Profile readProfile(Project project, String profileName);

			public boolean hasProfiles(Project project);

			public boolean writeProfile(Project project, Profile profile);

			public boolean removeProfile(Project project, Profile profile);

			public boolean hasProfile(Project context, String profileName);

		}

		public static class Profile {

			private static final String EXCEPTION_OVERWRITE = "Profile \"%s\" is unkown or can not be overwritten.";

			private static final String EXCEPTION_WRITEABLE = "Profile \"%s\" can not be written. Maybe it already exists.";

			@Override
			public String toString() {
				return "Profile [name=" + name + ", is_active=" + isActive + ", context=" + context.getName() + ", colors=" + featureColoring + "]";
			}

			public Profile(String name, Project context) {
				this.name = name;
				this.context = context;
			}

			private String name;

			private Project context;

			public String getName() {
				return name;
			}

			public void delete() {
				removeThisProfileFromSerializer(false);
			}

			public void setName(String name) {
				if (!this.name.equals(name)) {
					removeThisProfileFromSerializer(true);
					//context.profiles.remove(this.name);
					this.name = name;
					addThisProfileToSerializer();
					//context.profiles.put(name, this);
				}
			}

			/**
			 * 
			 */
			private void addThisProfileToSerializer() {
				if (!context.profileSerializer.writeProfile(context, this))
					throw new IllegalArgumentException(String.format(EXCEPTION_WRITEABLE, this.getName()));
			}

			/**
			 * 
			 */
			private void removeThisProfileFromSerializer(boolean forceDefaultProfileRemove) {
				if (this.name.equals("Default") && !forceDefaultProfileRemove)
					throw new IllegalArgumentException("Default profile can not be removed.");
				if (!context.profileSerializer.removeProfile(context, this))
					throw new IllegalArgumentException(String.format(EXCEPTION_OVERWRITE, this.getName()));
			}

			private PrintableMap<String, Color> featureColoring = new PrintableMap<>();

			public void setFeatureColor(String feature, Color color) {
				if (color.equals(Color.NO_COLOR) && featureColoring.containsKey(feature))
					featureColoring.remove(feature);
				else
					featureColoring.put(feature, color);
				if (context.profileSerializer.hasProfile(context, this.name)) {
					removeThisProfileFromSerializer(true);
				}
				if (!context.profileSerializer.writeProfile(context, this)) {
					throw new RuntimeException("Feature color change could not be stored.");
				}
			}

			public boolean hasFeatureColor(String feature) {
				return featureColoring.containsKey(feature);
			}

			public boolean removeFeatureColor(String feature) {
				if (!featureColoring.containsKey(feature))
					return false;
				else {
					featureColoring.remove(feature);
					if (context.profileSerializer.hasProfile(context, this.name)) {
						removeThisProfileFromSerializer(true);
					}
					context.profileSerializer.writeProfile(context, this);
					return true;
				}
			}

			public Color getColor(String feature) {
				if (!featureColoring.containsKey(feature))
					return Color.NO_COLOR;
				else {
					return featureColoring.get(feature);
				}
			}

			public Profile getActiveProfile() {
				for (Profile p : context.getProfiles())
					if (p.isActiveProfile())
						return p;
				throw new RuntimeException("No active profile found.");
			}

			boolean isActive = false;

			public boolean isActiveProfile() {
				return isActive;
			}
			
			public void internalSetAsActiveProfile() {
				isActive = true;
			}

			public void setAsActiveProfile() {
				//System.out.println("Request set active="+this);
				for (Profile p : context.profileSerializer.readProfiles(context)) {
					if (p.isActiveProfile()) {
						//System.out.println("unactive old="+p);
						p.isActive = false;
						context.profileSerializer.writeProfile(context, p);
					}
				}

				isActive = true;
				context.profileSerializer.writeProfile(context, this);
			}

			public List<String> getFeatures() {
				return Collections.unmodifiableList(new ArrayList<>(featureColoring.keySet()));
			}

			/**
			 * 
			 */
			public void clearColors() {
				featureColoring.clear();
				if (context.profileSerializer.hasProfile(context, this.name)) {
					removeThisProfileFromSerializer(true);
				}
				if (!context.profileSerializer.writeProfile(context, this)) {
					throw new RuntimeException("Feature color change could not be stored.");
				}				
			}

		
		}

		private void checkNameConflict(String profile) {
//			if (profiles.containsKey(profile))
//				throw new IllegalArgumentException("Duplicate profile");

		}

		/**
		 * @return
		 */
		public Profile getActiveProfile() {
			
			boolean foundDefaultProfile = false;
			for (Profile p : profileSerializer.readProfiles(this)) {
				if (p.isActive)
					return p;
				if (p.getName().equals("Default"))
					foundDefaultProfile = true;
				
			}
			if (foundDefaultProfile) {
				Profile p = getProfile("Default");
				p.setAsActiveProfile();
				return p;
			} else
				return addProfile("Default",  true);
		}

		/**
		 * @return
		 */

	}


}
