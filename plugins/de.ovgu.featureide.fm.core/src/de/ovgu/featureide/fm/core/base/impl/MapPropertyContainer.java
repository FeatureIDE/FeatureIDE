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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.core.base.IPropertyContainer;

/**
 * @author Marcus Pinnecke
 */
public class MapPropertyContainer implements IPropertyContainer {

	public MapPropertyContainer() {

	}

	public MapPropertyContainer(IPropertyContainer other) {
		setEntrySet(other.entrySet());
	}

	public static Object copyObject(Type type, Object value) {
		switch (type) {
		case BOOLEAN:
			return new Boolean((Boolean) value);
		case BYTE:
			return new Byte((Byte) value);
		case CHAR:
			return new Character((Character) value);
		case DOUBLE:
			return new Double((Double) value);
		case FLOAT:
			return new Float((Float) value);
		case INT:
			return new Integer((Integer) value);
		case LONG:
			return new Long((Long) value);
		case SHORT:
			return new Short((Short) value);
		case STRING:
			return new String((String) value);
		default:
			throw new RuntimeException("Unknown type:" + type);
		}
	}

	Map<String, Object> properties = new HashMap<>();
	Map<String, Type> types = new HashMap<>();

	protected String makeKey(String key) {
		return key.toLowerCase();
	}

	@SuppressWarnings("unchecked")
	@Override
	public <T> T get(String key, T defaultValue) {
		final String mapKey = makeKey(key);
		return properties.containsKey(mapKey) ? (T) properties.get(mapKey) : defaultValue;
	}

	@Override
	public Type getDataType(String key) throws NoSuchPropertyException {
		final String mapKey = makeKey(key);
		if (!properties.containsKey(mapKey)) {
			throw new NoSuchPropertyException(mapKey);
		} else {
			return types.get(mapKey);
		}
	}

	@SuppressWarnings("unchecked")
	@Override
	public <T> T get(String key) throws NoSuchPropertyException {
		final String mapKey = makeKey(key);
		if (!properties.containsKey(mapKey)) {
			throw new NoSuchPropertyException(mapKey);
		} else {
			return (T) properties.get(mapKey);
		}
	}

	@Override
	public boolean has(String key) {
		final String mapKey = makeKey(key);
		return properties.containsKey(mapKey);
	}

	@Override
	public Set<String> keySet() {
		return properties.keySet();
	}

	@Override
	public Set<Entry<String, Type, Object>> entrySet() {
		final HashSet<Entry<String, Type, Object>> entries = new HashSet<>();
		for (final String key : properties.keySet()) {
			entries.add(new Entry<String, IPropertyContainer.Type, Object>(key, types.get(key), properties.get(key)));
		}
		return entries;
	}

	@Override
	public void setEntrySet(Set<Entry<String, Type, Object>> entries) {
		properties.clear();
		types.clear();

		for (final Entry<String, Type, Object> entry : entries) {
			final String key = makeKey(new String(entry.getKey()));
			final Type type = entry.getType();
			final Object obj = copyObject(type, entry.getValue());
			properties.put(key, obj);
			types.put(key, type);
			System.out.println("key=" + key + ",type=" + type.toString() + ", val=" + obj);
		}
	}

	@Override
	public void remove(String key) throws NoSuchPropertyException {
		final String mapKey = makeKey(key);
		if (!properties.containsKey(mapKey)) {
			throw new NoSuchPropertyException(mapKey);
		}
		properties.remove(mapKey);
		types.remove(mapKey);
	}

	@Override
	public <T> void set(String key, Type type, T value) {
		final String mapKey = makeKey(key);
		properties.put(mapKey, value);
		types.put(mapKey, type);
	}

}
