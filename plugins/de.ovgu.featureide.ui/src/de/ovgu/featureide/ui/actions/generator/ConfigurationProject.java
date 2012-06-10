/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.actions.generator;

import org.eclipse.core.internal.resources.Project;
import org.eclipse.core.internal.resources.Workspace;
import org.eclipse.core.runtime.IPath;

/**
 * This is a workaround to create a new project
 * @author Jens Meinicke
 */
@SuppressWarnings("restriction")
public class ConfigurationProject extends Project {

	/**
	 * This is a workaround to have a access to the invisible constructor of the super class {@link Project}
	 * @param path The path of the project
	 * @param workspace The workspace of the new project
	 */
	protected ConfigurationProject(IPath path, Workspace workspace) {
		super(path, workspace);
		
	}


}
