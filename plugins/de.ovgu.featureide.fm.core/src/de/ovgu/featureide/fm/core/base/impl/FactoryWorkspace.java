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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.core.base.impl;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * A factory workspace maps feature model {@link IFeatureModelFormat formats} to a feature model {@link IFeatureModelFactory factory}. This way it can be
 * ensured that a specific factory is used when reading from a certain file type.
 *
 * @author Sebastian Krieter
 */
public final class FactoryWorkspace {

	private final Map<String, String> map;
	private String defaultFactoryID;

	private FactoryWorkspace(FactoryWorkspace oldWorkspace) {
		map = new HashMap<>(oldWorkspace.map);
		defaultFactoryID = oldWorkspace.defaultFactoryID;
	}

	FactoryWorkspace() {
		map = new HashMap<>();
	}

	public FactoryWorkspace(String defaultFactoryID) {
		map = new HashMap<>();
		this.defaultFactoryID = defaultFactoryID;
	}

	public String getDefaultFactoryID() {
		return defaultFactoryID;
	}

	public void setDefaultFactoryID(String defaultFactoryID) {
		this.defaultFactoryID = defaultFactoryID;
	}

	public String getID(IPersistentFormat<?> format) {
		return getID(format.getId());
	}

	public String getID(String formatID) {
		final String factoryID = map.get(formatID);
		return factoryID != null ? factoryID : defaultFactoryID;
	}

	public void assignID(IPersistentFormat<?> format, String factoryID) {
		assignID(format.getId(), factoryID);
	}

	public void assignID(String formatID, String factoryID) {
		map.put(formatID, factoryID);
	}

	public void removeID(IPersistentFormat<?> format) {
		removeID(format.getId());
	}

	public void removeID(String formatID) {
		map.remove(formatID);
	}

	public Map<String, String> getMap() {
		return Collections.unmodifiableMap(map);
	}

	@Override
	protected FactoryWorkspace clone() {
		return new FactoryWorkspace(this);
	}

}
