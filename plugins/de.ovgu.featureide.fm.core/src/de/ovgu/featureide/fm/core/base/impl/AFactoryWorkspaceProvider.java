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

/**
 * This {@link IFactoryWorkspaceProvider provider} maps paths to {@link FactoryWorkspace workspaces}.
 *
 * @author Sebastian Krieter
 */
public abstract class AFactoryWorkspaceProvider implements IFactoryWorkspaceProvider {

	protected final HashMap<String, FactoryWorkspace> projectMap = new HashMap<>();
	protected final FactoryWorkspace defaultWorkspace = new FactoryWorkspace();

	@Override
	public FactoryWorkspace getFactoryWorkspace(String path) {
		final FactoryWorkspace factoryWorkspace = projectMap.get(path);
		return factoryWorkspace != null ? factoryWorkspace : defaultWorkspace;
	}

	@Override
	public FactoryWorkspace getFactoryWorkspace() {
		return defaultWorkspace;
	}

	@Override
	public void addFactoryWorkspace(String path, FactoryWorkspace workspace) {
		projectMap.put(path, workspace);
	}

}
