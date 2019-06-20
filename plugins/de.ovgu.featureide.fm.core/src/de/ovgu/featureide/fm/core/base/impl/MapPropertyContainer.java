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
package de.ovgu.featureide.fm.core.base.impl;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.ovgu.featureide.fm.core.base.IPropertyContainer;

/**
 * @author Marcus Pinnecke
 */
public class MapPropertyContainer implements IPropertyContainer {

	public MapPropertyContainer() {}

	public MapPropertyContainer(IPropertyContainer other) {
		setProperties(other.getProperties());
	}

	protected Map<Entry, Entry> properties = new HashMap<>();

	@Override
	public String get(String key, String type, String defaultValue) {
		final Entry newEntry = new Entry(key, type);
		final Entry retrievedEntry = properties.get(newEntry);
		if (retrievedEntry == null) {
			newEntry.setValue(defaultValue);
			return defaultValue;
		}
		return retrievedEntry.getValue();
	}

	@Override
	public String get(String key, String type) throws NoSuchPropertyException {
		final Entry newEntry = new Entry(key, type);
		final Entry retrievedEntry = properties.get(newEntry);
		if (retrievedEntry == null) {
			throw new NoSuchPropertyException(newEntry.toString());
		}
		return retrievedEntry.getValue();
	}

	@Override
	public boolean has(String key, String type) {
		return properties.containsKey(new Entry(key, type));
	}

	@Override
	public Set<Entry> getProperties() {
		return properties.keySet();
	}

	@Override
	public Set<Entry> getProperties(String type) {
		final HashSet<Entry> filteredSet = new HashSet<>();
		for (final Entry entry : properties.keySet()) {
			if (Objects.equals(entry.getType(), type)) {
				filteredSet.add(entry);
			}
		}
		return filteredSet;
	}

	@Override
	public void setProperties(Collection<Entry> entries) {
		properties.clear();
		for (final Entry entry : entries) {
			final Entry copiedEntry = new Entry(entry);
			properties.put(copiedEntry, copiedEntry);
		}
	}

	@Override
	public Entry remove(String key, String type) {
		return properties.remove(new Entry(key, type));
	}

	@Override
	public void set(String key, String type, String value) {
		final Entry newEntry = new Entry(key, type);
		final Entry retrievedEntry = properties.get(newEntry);
		if (retrievedEntry == null) {
			newEntry.setValue(value);
			properties.put(newEntry, newEntry);
		} else {
			retrievedEntry.setValue(value);
		}
	}

	@Override
	public int hashCode() {
		int result = properties.size();
		for (final Entry entry : properties.keySet()) {
			result += entry.hashCode();
		}
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}

		final MapPropertyContainer other = (MapPropertyContainer) obj;
		return Objects.equals(properties, other.properties);
	}

}
