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
package de.ovgu.featureide.fm.core.base.impl;

/**
 * Provides a {@link FactoryWorkspace} for given path.<br/>
 * The purpose of this provider is to associate a certain factory workspace with a certain project / folder.
 * 
 * @author Sebastian Krieter
 */
public interface IFactoryWorkspaceProvider {

	FactoryWorkspace getFactoryWorkspace(String path);

	FactoryWorkspace getFactoryWorkspace();

	void addFactoryWorkspace(String path, FactoryWorkspace workspace);

	void save();

	boolean load();

}
