/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.core.builder;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.IFeatureProject;


/**
 * @brief Base interface of all composition tool classes.
 * 
 * Every plugin which extends the de.ovgu.featureide.core.composers needs to provide a class,
 * which implements this interface. Implementing this interface ensures that a given
 * composition tool meets the requirements for composition tools, which are used by the
 * @c ExtensibleFeatureProjectBuilder. This requirements are:
 * - Specifying a path for the composed files (usually "./build")
 * - Specifying a path for the source files (usually "./src")
 * - Specifying a path to the current configuration file (former equation file)
 * - Performing a full build for the current project with a given equation file 
 * 
 * @author Tom Brosch
 */
public interface IComposerExtensionClass {
	
	void initialize(IFeatureProject project);
	
	void performFullBuild(IFile equation);
	
	void clean();
	
}
