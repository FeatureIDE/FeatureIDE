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
import java.util.HashMap;
import java.util.Map;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * A factory workspace maps feature model {@link IFeatureModelFormat formats} to a feature model {@link IFeatureModelFactory factory}. This way it can be
 * ensured that a specific factory is used when reading from a certain file type.
 *
 * @author Sebastian Krieter
 */
public class FactoryWorkspace {

	protected final Map<String, String> map;

	private String defaultFactoryID;

	public FactoryWorkspace(FactoryWorkspace oldWorkspace) {
		defaultFactoryID = oldWorkspace.defaultFactoryID;
		map = new HashMap<>(oldWorkspace.map);
	}

	public FactoryWorkspace() {
		defaultFactoryID = DefaultFeatureModelFactory.ID;
		map = new HashMap<>();
	}

	public String getID(IPersistentFormat<IFeatureModel> format) {
		return getID(format.getId());
	}

	public String getID(String formatID) {
		final String factoryID = map.get(formatID);
		return factoryID == null ? defaultFactoryID : factoryID;
	}

	public String getDefaultFactoryID() {
		return defaultFactoryID;
	}

	public void setDefaultFactoryID(String defaultFactoryID) {
		this.defaultFactoryID = defaultFactoryID;
	}

	public void assignID(IFeatureModelFormat format, String factoryID) {
		assignID(format.getId(), factoryID);
	}

	public void assignID(String formatID, String factoryID) {
		map.put(formatID, factoryID);
	}

	public Map<String, String> getMap() {
		return Collections.unmodifiableMap(map);
	}

	@Override
	protected Object clone() throws CloneNotSupportedException {
		return new FactoryWorkspace(this);
	}

}
