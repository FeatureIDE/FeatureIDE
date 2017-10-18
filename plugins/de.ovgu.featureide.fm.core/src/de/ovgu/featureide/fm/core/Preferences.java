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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.osgi.service.prefs.BackingStoreException;

/**
 * Holds all preference values for FeatureIDE.</br> Stores the values persistently for each workspace. Loads all the values when this class is loaded.
 *
 * @author Sebastian Krieter
 */
public abstract class Preferences {

	public static final int COMPLETION_NONE = 0, COMPLETION_ONE_CLICK = 1, COMPLETION_OPEN_CLAUSES = 2, SCHEME_LONG = 0, SCHEME_SHORT = 1;

	private static final IEclipsePreferences preferences = InstanceScope.INSTANCE.getNode("de.ovgu.featureide.fm.core");

	public static int defaultCompletion;

	static {
		final String pref = preferences.get("configCompletion", Integer.toString(COMPLETION_ONE_CLICK));
		defaultCompletion = castToInt(pref, COMPLETION_ONE_CLICK);
	}

	/**
	 * @return the defaultCompletion
	 */
	public static int getDefaultCompletion() {
		return defaultCompletion;
	}

	public static void setDefaultCompletion(int defaultCompletion) {
		Preferences.defaultCompletion = defaultCompletion;
		store("configCompletion", defaultCompletion);
	}

	private static int castToInt(String pref, int defaultValue) {
		try {
			return Integer.parseInt(pref);
		} catch (final Exception e) {
			return defaultValue;
		}
	}

	private static void store(String pref, int value) {
		preferences.put(pref, Integer.toString(value));
		flush();
	}

	private static void flush() {
		try {
			preferences.flush();
		} catch (final BackingStoreException e) {
			Logger.logError(e);
		}
	}
}
