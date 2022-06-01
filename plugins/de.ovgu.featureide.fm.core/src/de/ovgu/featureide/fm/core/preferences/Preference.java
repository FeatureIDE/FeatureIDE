/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.preferences;

import java.util.Objects;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.osgi.service.prefs.BackingStoreException;

import de.ovgu.featureide.fm.core.Logger;

/**
 * Stores a preference of type T.
 *
 * @author Sebastian Krieter
 */
public abstract class Preference<T> {

	private static final IEclipsePreferences preferences = InstanceScope.INSTANCE.getNode("de.ovgu.featureide.fm.core");

	private static void store(String key, String value) {
		preferences.put(key, value);
		try {
			preferences.flush();
		} catch (final BackingStoreException e) {
			Logger.logError(e);
		}
	}

	protected final String name;
	protected T value;

	protected Preference(String name) {
		this.name = name;
		try {
			this.value = parse(preferences.get(name, serialize(getDefault())));
		} catch (final Exception e) {
			this.value = getDefault();
		}
	}

	public abstract T getDefault();

	public T resetToDefault() {
		final T defaultValue = getDefault();
		set(defaultValue);
		return defaultValue;
	}

	public String getName() {
		return name;
	}

	protected abstract T parse(String value);

	protected String serialize(T value) {
		return String.valueOf(value);
	}

	public synchronized void set(T value) {
		this.value = value;
		store(name, serialize(value));
	}

	public T get() {
		return value;
	}

	@Override
	public int hashCode() {
		return Objects.hash(name);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}
		return Objects.equals(name, ((Preference<?>) obj).name);
	}

}
