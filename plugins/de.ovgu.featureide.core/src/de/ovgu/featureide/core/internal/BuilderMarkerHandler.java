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
package de.ovgu.featureide.core.internal;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;

import de.ovgu.featureide.core.IBuilderMarkerHandler;

/**
 * The MarkerHandler encapsulates creating and removing markers.
 *
 * @author Sebastian Krieter
 */
public class BuilderMarkerHandler implements IBuilderMarkerHandler {

	protected final IProject project;

	public BuilderMarkerHandler(IProject project) {
		this.project = project;
	}

	@Override
	public void createBuilderMarker(IResource resource, String message, int lineNumber, int severity) {
		EclipseMarkerHandler.createBuilderMarker((resource != null) ? resource : project, message, lineNumber, severity);
	}

	@Override
	public void deleteBuilderMarkers(IResource resource, int depth) {
		EclipseMarkerHandler.deleteBuilderMarkers(resource, depth);
	}

	public void createConfigurationMarker(IResource resource, String message, int lineNumber, int severity) {
		EclipseMarkerHandler.createConfigurationMarker(resource, message, lineNumber, severity);
	}

	public void deleteConfigurationMarkers(IResource resource, int depth) {
		EclipseMarkerHandler.deleteConfigurationMarkers(resource, depth);
	}

}
