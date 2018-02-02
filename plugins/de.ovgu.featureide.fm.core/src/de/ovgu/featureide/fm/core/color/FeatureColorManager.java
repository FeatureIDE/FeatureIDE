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
package de.ovgu.featureide.fm.core.color;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
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

import de.ovgu.featureide.fm.core.FMCorePlugin;
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

	protected static final List<IEventListener> colorListener = new LinkedList<>();

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
		removeColorScheme(featureModel, getCurrentColorScheme(featureModel).getName());
	}

	public static void removeColorScheme(final IFeatureModel featureModel, final String currentName) {
		final IProject project = getProject(featureModel);
		final IFolder profileFolder = project.getFolder(".profiles");
		if (!profileFolder.exists()) {
			return;
		}
		if (DefaultColorScheme.defaultName.equals(currentName)) {
			throw new RuntimeException("Default color scheme cannot be removed!");
		}
		final ColorScheme removedColorScheme = colorSchemes.get(project).remove(currentName);
		final IFile file = profileFolder.getFile(currentName + ".profile");
		if (!file.exists()) {
			Logger.logWarning(file + " does not exist");
			return;
		}
		try {
			file.delete(true, new NullProgressMonitor());
		} catch (final CoreException e) {
			Logger.logError(e);
		}
		if (removedColorScheme.isCurrent()) {
			setActive(project, DefaultColorScheme.defaultName, true);
		}

		// Update project explorer
		try {
			project.touch(null);
			project.refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		final ArrayList<IFeature> changedFeatures = new ArrayList<IFeature>();
		for (final String featureName : removedColorScheme.getColors().keySet()) {
			changedFeatures.add(featureModel.getFeature(featureName));
		}
		notifyColorChange(changedFeatures);
	}

	/**
	 * Checks whether the given scheme is active.
	 *
	 * @param newProfileColorSchemeName
	 * @return
	 */
	public static boolean isCurrentColorScheme(IFeatureModel featureModel, String schmeName) {
		final IProject project = getProject(featureModel);
		final Map<String, ColorScheme> currentSchemes = colorSchemes.get(project);
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
		IProject project;
		// Fix for #398
		try {
			project = getProject(featureModel);
		} catch (final NullPointerException e) {
			return new DefaultColorScheme();
		}

		if (!colorSchemes.containsKey(project)) {
			initColorSchemes(project, featureModel);
		}
		Map<String, ColorScheme> currentSchemes = colorSchemes.get(project);
		if (currentSchemes.isEmpty()) {
			initColorSchemes(project, featureModel);
			currentSchemes = colorSchemes.get(project);
		}

		for (final ColorScheme cs : currentSchemes.values()) {
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
		for (final ColorScheme cs : getColorSchemes(model)) {
			if (cs.isDefault()) {
				return cs;
			}
		}
		throw new RuntimeException("There must be a default color scheme!");
	}

	/**
	 * Initializes and loads all color schemes for the given project.
	 */
	private static void initColorSchemes(IProject project, IFeatureModel featureModel) {
		final Map<String, ColorScheme> newEntry = new HashMap<>();
		newEntry.put(DefaultColorScheme.defaultName, new DefaultColorScheme());
		colorSchemes.put(project, newEntry);
		featureModel.getRenamingsManager().addListener(INSTANCE);

		final IFolder profileFolder = project.getFolder(".profiles");
		if (!profileFolder.exists()) {
			return;
		}
		try {
			for (final IResource res : profileFolder.members()) {
				final String ext = res.getFileExtension();
				if (ext == null) {
					throw new RuntimeException("Unexpected null reference");
				}

				if ((res instanceof IFile) && ext.equals("profile")) {
					readColors(newEntry, res);
				}
			}
		} catch (final CoreException e) {
			Logger.logError(e);
		}
	}

	/**
	 * Reads the colors from the given file.
	 */
	private static void readColors(Map<String, ColorScheme> newEntry, IResource res) {
		try (BufferedReader in = new BufferedReader(new FileReader(new File(res.getLocationURI())))) {
			final String name = res.getName().substring(0, res.getName().lastIndexOf('.'));
			final ColorScheme newCs = new ColorScheme(name);
			newEntry.put(newCs.getName(), newCs);
			String line = in.readLine();
			if (line == null) {
				throw new RuntimeException("Unexpected null reference");
			}
			if (line.equals("true")) {
				setActive(res.getProject(), name, false);
			}

			while ((line = in.readLine()) != null) {
				final String[] split = line.split("=");
				try {
					if (split.length != 2) {
						continue;
					}
					newCs.setColor(split[0], FeatureColor.valueOf(split[1]));
				} catch (final IllegalArgumentException e) {
					Logger.logError("Color not found", e);
				}
			}
		} catch (final IOException e) {
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
		final IFolder profileFolder = project.getFolder(".profiles");
		if (!profileFolder.exists()) {
			try {
				profileFolder.create(true, true, new NullProgressMonitor());
			} catch (final CoreException e) {
				Logger.logError(e);
			}
		}
		final IFile file = profileFolder.getFile(colorScheme.getName() + ".profile");
		if (!file.exists()) {
			try {
				new File(file.getLocationURI()).createNewFile();
			} catch (final IOException e) {
				Logger.logError(e);
			}
		}

		try (PrintWriter out = new PrintWriter(new FileWriter(new File(file.getLocationURI()), false), true)) {
			out.println(colorScheme.isCurrent());
			for (final Entry<String, FeatureColor> entry : colorScheme.getColors().entrySet()) {
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
		final IProject project = getProject(featureModel);
		if (!colorSchemes.containsKey(project)) {
			initColorSchemes(project, featureModel);
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
		final java.nio.file.Path file = featureModel.getSourceFile();
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		final IPath location = Path.fromOSString(file.toAbsolutePath().toString());
		final IFile iFile = workspace.getRoot().getFileForLocation(location);
		try {
			return iFile.getProject();
		} catch (final NullPointerException e) {
			Logger.logWarning(location.toOSString());
			throw e;
		}
	}

	/**
	 * Creates a new color scheme for with the given name.
	 */
	public static void newColorScheme(IFeatureModel featureModel, String csName) {
		final IProject project = getProject(featureModel);
		final ColorScheme newColorScheme = new ColorScheme(csName);
		final Map<String, ColorScheme> currentSchemes = colorSchemes.get(project);
		if (currentSchemes.containsKey(csName)) {
			throw new RuntimeException("scheme " + csName + " already exists");
		}
		// featureModel.getRenamingsManager().addListener(INSTANCE);
		currentSchemes.put(csName, newColorScheme);
	}

	/**
	 * Checks whether there is a color scheme with the given name.
	 */
	public static boolean hasColorScheme(IFeatureModel featureModel, String csName) {
		final IProject project = getProject(featureModel);
		return colorSchemes.get(project).containsKey(csName);
	}

	/**
	 * Changes the name of the color scheme.
	 */
	public static void renameColorScheme(IFeatureModel featureModel, String newName) {
		renameColorScheme(featureModel, getCurrentColorScheme(featureModel).getName(), newName);
	}

	public static void renameColorScheme(IFeatureModel featureModel, String oldName, String newName) {
		final IProject project = getProject(featureModel);
		final Map<String, ColorScheme> currentColorSchemes = colorSchemes.get(project);
		final ColorScheme scheme = currentColorSchemes.get(oldName);
		removeColorScheme(featureModel, oldName);
		scheme.setName(newName);
		currentColorSchemes.put(newName, scheme);
		writeColors(project, scheme);
	}

	/**
	 * Activates the color scheme with the given name.
	 */
	public static void setActive(IFeatureModel fm, String collName) {
		final IProject project = getProject(fm);
		setActive(project, collName, true);
		fm.handleModelDataChanged();
	}

	/**
	 * Activates the color scheme with the given name.
	 */
	public static void setActive(IProject project, String collName, boolean write) {
		final Map<String, ColorScheme> currentSchemes = colorSchemes.get(project);
		if (!currentSchemes.containsKey(collName)) {
			throw new RuntimeException("tried to activate scheme " + collName);
		}
		for (final Entry<String, ColorScheme> cs : currentSchemes.entrySet()) {
			final ColorScheme scheme = cs.getValue();
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
		final Collection<ColorScheme> currentColorSchemes = getColorSchemes(model);
		for (final ColorScheme colorScheme : currentColorSchemes) {
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

	/**
	 * Add a listener to the ColorChange Notification List.
	 *
	 * @param listener
	 */
	public static void addListener(IEventListener listener) {
		if (!colorListener.contains(listener)) {
			colorListener.add(listener);
		}
	}

	/**
	 * Notify all listener that the color of features has changed
	 *
	 * @param features All features that colors were changed
	 */
	public static void notifyColorChange(ArrayList<IFeature> features) {
		for (final IEventListener listener : colorListener) {
			try {
				listener.propertyChange(new FeatureIDEEvent(features, EventType.COLOR_CHANGED));
			} catch (final Throwable e) {
				Logger.logError(e);
			}
		}
	}

	/**
	 * Notify all listener that the color of a feature has changed
	 *
	 * @param features All features that colors were changed
	 */
	public static void notifyColorChange(IFeature feature) {
		for (final IEventListener listener : colorListener) {
			try {
				listener.propertyChange(new FeatureIDEEvent(feature, EventType.COLOR_CHANGED));
			} catch (final Throwable e) {
				Logger.logError(e);
			}
		}
	}

	/**
	 * Removes the listener from the notification list.
	 *
	 * @param listener
	 */
	public static void removeListener(IEventListener listener) {
		colorListener.remove(listener);
	}

}
