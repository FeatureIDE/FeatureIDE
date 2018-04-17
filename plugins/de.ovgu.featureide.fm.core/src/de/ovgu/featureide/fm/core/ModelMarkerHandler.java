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
package de.ovgu.featureide.fm.core;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

/**
 * The MarkerHandler encapsulates creating and removing markers.
 *
 * @author Thomas Thuem
 *
 */
public class ModelMarkerHandler<T extends IResource> implements IModelMarkerHandler {

	private static final String MODEL_MARKER = PluginID.PLUGIN_ID + ".featureModelMarker";

	private final T modelFile;

	public ModelMarkerHandler(T modelFile) {
		this.modelFile = modelFile;
	}

	public T getModelFile() {
		return modelFile;
	}

	@Override
	public void createModelMarker(String message, int severity, int lineNumber) {
		try {
			final IResource resource = modelFile.exists() ? modelFile : modelFile.getProject();
			for (final IMarker m : resource.findMarkers(MODEL_MARKER, false, IResource.DEPTH_ZERO)) {
				if (m.getAttribute(IMarker.MESSAGE, "").equals(message)) {
					return;
				}
			}
			final IMarker marker = resource.createMarker(MODEL_MARKER);
			if (marker.exists()) {
				marker.setAttribute(IMarker.MESSAGE, message);
				marker.setAttribute(IMarker.SEVERITY, severity);
				marker.setAttribute(IMarker.LINE_NUMBER, lineNumber);
			}
		} catch (final CoreException e) {
			Logger.logError(e);
		}
	}

	@Override
	public void deleteAllModelMarkers() {
		if (modelFile.getProject().isAccessible()) {
			deleteMarkers(modelFile.getProject());
		}
		if (modelFile.exists()) {
			deleteMarkers(modelFile);
		}
	}

	private void deleteMarkers(IResource resource) {
		try {
			resource.deleteMarkers(MODEL_MARKER, false, IResource.DEPTH_ZERO);
		} catch (final CoreException e) {
			Logger.logError(e);
		}
	}

	@Override
	public boolean hasModelMarkers() {
		return hasModelMarkers(modelFile.getProject()) || hasModelMarkers(modelFile);
	}

	private boolean hasModelMarkers(IResource resource) {
		try {
			return resource.findMarkers(MODEL_MARKER, false, IResource.DEPTH_ZERO).length > 0;
		} catch (final CoreException e) {
			Logger.logError(e);
		}
		return true;
	}

}
