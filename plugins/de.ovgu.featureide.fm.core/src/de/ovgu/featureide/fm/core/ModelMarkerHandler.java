/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

/**
 * The MarkerHandler encapsulates creating and removing markers.
 * 
 * @author Thomas Thuem
 * 
 */
public class ModelMarkerHandler implements IModelMarkerHandler {
	
	private static final String MODEL_MARKER = FMCorePlugin.PLUGIN_ID + ".featureModelMarker";
	
	public ModelMarkerHandler(IResource modelFile) {
		this.modelFile = modelFile;
		this.project = modelFile.getProject();
	}

	protected final IResource modelFile;

	protected final IProject project;

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.internal.IMarkerHandler#createModelMarker(java.lang.String,
	 *      int)
	 */
	public void createModelMarker(String message, int severity, int lineNumber) {
		try {
			IResource resource = modelFile.exists() ? modelFile : project;
			for (IMarker m : resource.findMarkers(MODEL_MARKER, false, IResource.DEPTH_ZERO)) {
				if (m.getAttribute(IMarker.MESSAGE, "").equals(message)) {
					return;
				}
			}
			IMarker marker = resource.createMarker(MODEL_MARKER);
			if (marker.exists()) {
				marker.setAttribute(IMarker.MESSAGE, message);
				marker.setAttribute(IMarker.SEVERITY, severity);
				marker.setAttribute(IMarker.LINE_NUMBER, lineNumber);
			}
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.internal.IMarkerHandler#deleteAllModelMarkers()
	 */
	public void deleteAllModelMarkers() {
		try {
			if (project.isAccessible())
				project
						.deleteMarkers(MODEL_MARKER, false,
								IResource.DEPTH_ZERO);
			if (modelFile.exists())
				modelFile.deleteMarkers(MODEL_MARKER, false,
						IResource.DEPTH_ZERO);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.internal.IMarkerHandler#hasModelMarkers()
	 */
	public boolean hasModelMarkers() {
		return hasModelMarkers(project) || hasModelMarkers(modelFile);
	}

	private boolean hasModelMarkers(IResource resource) {
		try {
			return resource.findMarkers(MODEL_MARKER, false,
					IResource.DEPTH_ZERO).length > 0;
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return true;
	}

}
