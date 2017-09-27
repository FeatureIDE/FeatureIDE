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

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.ovgu.featureide.fm.core.base.IPropertyContainer;

public class UnmodifiablePropertyContainer implements IPropertyContainer {

	private final IPropertyContainer container;

	static UnsupportedOperationException exception =
		new UnsupportedOperationException("Manipulation is not allowed. This is an unmodifiable property container");

	public UnmodifiablePropertyContainer(IPropertyContainer container) {
		this.container = container;
	}

	@Override
	public <T> T get(String key, T defaultValue) {
		return container.get(key, defaultValue);
	}

	@Override
	public Type getDataType(String key) throws NoSuchPropertyException {
		return container.getDataType(key);
	}

	@Override
	public <T> T get(String key) throws NoSuchPropertyException {
		return container.get(key);
	}

	@Override
	public boolean has(String key) {
		return container.has(key);
	}

	@Override
	public Set<String> keySet() {
		final Set<String> set = new HashSet<>();
		for (final String s : container.keySet()) {
			set.add(new String(s));
		}
		return set;
	}

	@Override
	public Set<Entry<String, Type, Object>> entrySet() {
		return Collections.unmodifiableSet(container.entrySet());
	}

	@Override
	public void setEntrySet(Set<Entry<String, Type, Object>> entries) {
		throw exception;
	}

	@Override
	public void remove(String key) throws NoSuchPropertyException {
		throw exception;
	}

	@Override
	public <T> void set(String key, Type type, T value) {
		throw exception;
	}

}
