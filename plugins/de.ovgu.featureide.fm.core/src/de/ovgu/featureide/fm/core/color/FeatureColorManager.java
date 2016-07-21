/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.color;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;

/**
 * Manages colors assigned to features.
 * 
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureColorManager implements IEventListener {
	
	private static final FeatureColorManager INSTANCE = new FeatureColorManager();

	private static final Map<IProject, Map<String, ColorScheme>> colorSchemes = new HashMap<>();

	/**
	 * Returns the current color of the given feature.
	 */
	public static FeatureColor getColor(IFeature feature) {
		return getCurrentColorScheme(feature).getColor(feature);
	}

	
	/**
	 * Sets the feature color to the given index.
	 */
	public static void setColor(IFeature feature, int index) {
		setColor(feature, FeatureColor.getColor(index));	
	}
	
	/**
	 * Sets the feature color to the given color.
	 */
	public static void setColor(IFeature feature, FeatureColor color) {
		getCurrentColorScheme(feature).setColor(feature, color);
		writeColors(getProject(feature), getCurrentColorScheme(feature));
	}

	/**
	 * Checks whether the current scheme is the default scheme without colors.
	 */
	public static boolean isDefault(IFeatureModel featureModel) {
		return getCurrentColorScheme(featureModel).isDefault();
	}

	/**
	 * Deletes the profile with the given name.
	 */
	public static void removeCurrentColorScheme(final IFeatureModel featureModel) {
		final IProject project = getProject(featureModel);
		final IFolder profileFolder = project.getFolder(".profiles");
		if (!profileFolder.exists()) {
			return;
		}
		final String currentName = getCurrentColorScheme(featureModel).getName();
		if (DefaultColorScheme.defaultName.equals(currentName)) {
			throw new RuntimeException("Default color schme cannot be removed!");
		}
		colorSchemes.get(project).remove(currentName);
		final IFile file = profileFolder.getFile(currentName + ".profile");
		if (!file.exists()) {
			Logger.logWarning(file  + " does not exist");
			return;
		}
		try {
			file.delete(true, new NullProgressMonitor());
		} catch (CoreException e) {
			Logger.logError(e);
		}
		setActive(project, DefaultColorScheme.defaultName, true);
	}

	/**
	 * Checks whether the given scheme is active.
	 * @param newProfileColorSchemeName
	 * @return
	 */
	public static boolean isCurrentColorScheme(IFeatureModel featureModel, String schmeName) {
		IProject project = getProject(featureModel);
		Map<String, ColorScheme> currentSchemes = colorSchemes.get(project);
		return currentSchemes.get(schmeName).isCurrent();
	}
	
	/**
	 * Returns the current color scheme.
	 */
	public static ColorScheme getCurrentColorScheme(IFeature feature) {
		if (feature == null) {
			return new DefaultColorScheme();
		}
		return getCurrentColorScheme(feature.getFeatureModel());
	}

	/**
	 * Returns the current color scheme.
	 */
	public static ColorScheme getCurrentColorScheme(IFeatureModel featureModel) {
		IProject project = getProject(featureModel);
		if (project == null) {
			// bad workaround 
			return new DefaultColorScheme();
		}
		
		if (!colorSchemes.containsKey(project)) {
			initColorSchemes(project);
		}
		Map<String, ColorScheme> currentSchemes = colorSchemes.get(project);
		if (currentSchemes.isEmpty()) {
			initColorSchemes(project);
			currentSchemes = colorSchemes.get(project);
		}
		
		for (ColorScheme cs : currentSchemes.values()) {
			if (cs.isCurrent()) {
				return cs;
			}
		}
		return new DefaultColorScheme();
	}
	
	/**
	 * Returns the default color scheme.
	 */
	public static ColorScheme getDefaultColorScheme(IFeatureModel model) {
		for (ColorScheme cs : getColorSchemes(model)) {
			if (cs.isDefault()) {
				return cs;
			}
		}
		throw new RuntimeException("There must be a default color scheme!");
	}

	/**
	 * Initializes and loads all color schemes for the given project.
	 */
	private static void initColorSchemes(IProject project) {
		Map<String, ColorScheme> newEntry = new HashMap<>();
		newEntry.put(DefaultColorScheme.defaultName, new DefaultColorScheme());
		colorSchemes.put(project, newEntry);
		
		IFolder profileFolder = project.getFolder(".profiles");
		if (!profileFolder.exists()) {
			return;
		}
		try {
			for (IResource res : profileFolder.members()) {
				final String ext = res.getFileExtension();
				if (ext == null)
					throw new RuntimeException("Unexpected null reference");
				
				if (res instanceof IFile && ext.equals("profile")) {
					readColors(newEntry, res);
				}
			}
		} catch (CoreException e) {
			Logger.logError(e);
		}
	}

	/**
	 * Reads the colors from the given file.
	 */
	private static void readColors(Map<String, ColorScheme> newEntry, IResource res) {
		try (BufferedReader in = new BufferedReader(new FileReader(new File(res.getLocationURI())))) {
			final String name = res.getName().substring(0, res.getName().lastIndexOf('.'));
			ColorScheme newCs = new ColorScheme(name);
			newEntry.put(newCs.getName(), newCs);
			String line = in.readLine();
			if (line == null)
				throw new RuntimeException("Unexpected null reference");
			if (line.equals("true")) {
				setActive(res.getProject(), name, false);
			}
			
			while ((line = in.readLine()) != null) {
				String[] split = line.split("=");
				try {
					if (split.length != 2) {
						continue;
					}
					newCs.setColor(split[0], FeatureColor.valueOf(split[1]));					
				} catch (IllegalArgumentException e) {
					Logger.logError("Color not found", e);
				}
			}
		} catch (IOException e) {
			Logger.logError(e);
		}
	}
	
	/**
	 * Writes the given color scheme to a file.
	 */
	private static void writeColors(IProject project, ColorScheme colorScheme) {
		if (colorScheme.isDefault()) {
			return;
		}
		IFolder profileFolder = project.getFolder(".profiles");
		if (!profileFolder.exists()) {
			try {
				profileFolder.create(true, true, new NullProgressMonitor());
			} catch (CoreException e) {
				Logger.logError(e);
			}
		}
		IFile file = profileFolder.getFile(colorScheme.getName() + ".profile");
		if (!file.exists()) {
			try {
				new File(file.getLocationURI()).createNewFile();
			} catch (IOException e) {
				Logger.logError(e);
			}
		}
		
		try (PrintWriter out = new PrintWriter(new FileWriter(new File(file.getLocationURI()), false), true)) {
			out.println(colorScheme.isCurrent());
			for (Entry<String, FeatureColor> entry : colorScheme.getColors().entrySet()) {
				out.print(entry.getKey());
				out.print('=');
				out.println(entry.getValue());
			}
			
			file.refreshLocal(IResource.DEPTH_ZERO, new NullProgressMonitor());
		} catch (IOException | CoreException e) {
			Logger.logError(e);
		}
	}

	/**
	 * Returns all profiles for the given model.
	 */
	public static Collection<ColorScheme> getColorSchemes(IFeatureModel featureModel) {
		IProject project = getProject(featureModel);
		if (!colorSchemes.containsKey(project)) {
			initColorSchemes(project);
		}
		return colorSchemes.get(project).values();
	}

	/**
	 * Gets the associated project for the given feature.
	 */
	private static IProject getProject(IFeature feature) {
		return getProject(feature.getFeatureModel());
	}
	
	private static IProject getProject(IFeatureModel featureModel) {
		File file = featureModel.getSourceFile();
		IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IPath location = Path.fromOSString(file.getAbsolutePath());
		IFile iFile = workspace.getRoot().getFileForLocation(location);
		try {
			return iFile.getProject();
		} catch (NullPointerException e) {
			Logger.logWarning(location.toOSString());
			throw e;
		}
	}

	/**
	 * Creates a new color scheme for with the given name.
	 */
	public static void newColorScheme(IFeatureModel featureModel, String csName) {
		IProject project = getProject(featureModel);
		ColorScheme newColorScheme = new ColorScheme(csName);
		Map<String, ColorScheme> currentSchemes = colorSchemes.get(project);
		if (currentSchemes.containsKey(csName)) {
			throw new RuntimeException("scheme " + csName + " already exists");
		}
		featureModel.getRenamingsManager().addListener(INSTANCE);
		currentSchemes.put(csName, newColorScheme);
	}

	/**
	 * Checks whether there is a color scheme with the given name.
	 */
	public static boolean hasColorScheme(IFeatureModel featureModel, String csName) {
		IProject project = getProject(featureModel);
		return colorSchemes.get(project).containsKey(csName);
	}

	/**
	 * Changes the name of the color scheme.
	 */
	public static void renameColorScheme(IFeatureModel featureModel, String newName) {
		IProject project = getProject(featureModel);
		Map<String, ColorScheme> currentColorSchemes = colorSchemes.get(project);
		String oldName = getCurrentColorScheme(featureModel).getName();
		ColorScheme scheme = currentColorSchemes.get(oldName);
		removeCurrentColorScheme(featureModel);
		scheme.setName(newName);
		currentColorSchemes.put(newName, scheme);
		writeColors(project, scheme);
	}

	/**
	 * Activates the color scheme with the given name.
	 */
	public static void setActive(IFeatureModel fm, String collName) {
		IProject project = getProject(fm);
		setActive(project, collName, true);
		fm.handleModelDataChanged();
	}
	
	/**
	 * Activates the color scheme with the given name.
	 */
	public static void setActive(IProject project, String collName, boolean write) {
		Map<String, ColorScheme> currentSchemes = colorSchemes.get(project);
		if (!currentSchemes.containsKey(collName)) {
			throw new RuntimeException("tried to activate scheme " + collName);
		}
		for (Entry<String, ColorScheme> cs : currentSchemes.entrySet()) {
			ColorScheme scheme = cs.getValue();
			if (cs.getKey().equals(collName)) {
				if (!scheme.isCurrent()) {
					scheme.setCurrent(true);
					if (write) {
						writeColors(project, scheme);
					}
				}
			} else {
				if (scheme.isCurrent()) {
					scheme.setCurrent(false);
					if (write) {
						writeColors(project, scheme);
					}
				}
			}
			
		}
	}

	/**
	 * Performs the feature renaming.
	 */
	public static void renameFeature(IFeatureModel model, String oldName, String newName) {
		Collection<ColorScheme> currentColorSchemes = getColorSchemes(model);
		for (ColorScheme colorScheme : currentColorSchemes) {
			colorScheme.renameFeature(oldName, newName);
			writeColors(getProject(model), colorScheme);
		}
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		if (event.getEventType() == EventType.FEATURE_NAME_CHANGED) {
			renameFeature(((IFeature) event.getSource()).getFeatureModel(), (String) event.getOldValue(), (String) event.getNewValue());
		}
	}

}
