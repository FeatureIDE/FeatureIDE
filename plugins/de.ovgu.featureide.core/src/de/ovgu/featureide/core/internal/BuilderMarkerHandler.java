/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.core.internal;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IBuilderMarkerHandler;

/**
 * The MarkerHandler encapsulates creating and removing markers.
 * 
 * @author Thomas Thuem
 * 
 */
public class BuilderMarkerHandler implements IBuilderMarkerHandler {

	private static final String BUILDER_MARKER = CorePlugin.PLUGIN_ID
			+ ".builderProblemMarker";

	private static final String CONFIGURATION_MARKER = CorePlugin.PLUGIN_ID
			+ ".configurationProblemMarker";

	public BuilderMarkerHandler(IProject project) {
		this.project = project;
	}

	protected final IProject project;

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.internal.IMarkerHandler#createBuilderMarker(org
	 * .eclipse.core.resources.IResource, java.lang.String, int, int)
	 */
	public void createBuilderMarker(IResource resource, String message,
			int lineNumber, int severity) {
		if (resource != null) {
			// for creating and deleting markers a synchronized file is
			// neccessary
			try {
				resource.refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		} else
			resource = project;

		// prevent duplicate error markers (e.g. caused by changing a jak file
		// that refines a non-valid jak file)
		deleteIfExists(resource, message, lineNumber, severity);

		try {
			IMarker marker = resource.createMarker(BUILDER_MARKER);
			marker.setAttribute(IMarker.MESSAGE, message);
			marker.setAttribute(IMarker.SEVERITY, severity);
			marker.setAttribute(IMarker.LINE_NUMBER, lineNumber);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	private void deleteIfExists(IResource resource, String message,
			int lineNumber, int severity) {
		try {
			IMarker[] markers = resource.findMarkers(BUILDER_MARKER, false,
					IResource.DEPTH_ZERO);
			if (!resource.exists())
				return;
			for (IMarker marker : markers) {
				if (marker.getAttribute(IMarker.MESSAGE).equals(message)
						&& (Integer) marker.getAttribute(IMarker.LINE_NUMBER) == lineNumber
						&& (Integer) marker.getAttribute(IMarker.SEVERITY) == severity) {
					marker.delete();
				}
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.internal.IMarkerHandler#deleteBuilderMarkers(
	 * org.eclipse.core.resources.IResource, int)
	 */
	public void deleteBuilderMarkers(IResource resource, int depth) {
		if (resource != null && resource.exists()) {
			try {
				resource.deleteMarkers(BUILDER_MARKER, false, depth);
			} catch (CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		}
	}

	public void createConfigurationMarker(IResource resource, String message,
			int lineNumber, int severity) {
		try {
			resource.refreshLocal(IResource.DEPTH_ZERO, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		if (hasMarker(resource, message, lineNumber)) {
			return;
		}
		try {
			IMarker marker = resource.createMarker(CONFIGURATION_MARKER);
			marker.setAttribute(IMarker.MESSAGE, message);
			marker.setAttribute(IMarker.SEVERITY, severity);
			if (lineNumber == -1) {
				lineNumber = 1;
			}
			marker.setAttribute(IMarker.LINE_NUMBER, lineNumber);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * @param resource
	 * @param message
	 * @param lineNumber
	 * @return
	 */
	private boolean hasMarker(IResource resource, String message, int lineNumber) {
		try {
			IMarker[] marker = resource.findMarkers(CONFIGURATION_MARKER, false, IResource.DEPTH_ZERO);
			if (marker != null) {
				for (IMarker m : marker) {
					if (m.getAttribute(IMarker.MESSAGE).equals(message) &&
							m.getAttribute(IMarker.LINE_NUMBER).equals(lineNumber)) {
						return true;
					}
				}
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return false;
	}

	public void deleteConfigurationMarkers(IResource resource, int depth) {
		try {
			resource.deleteMarkers(CONFIGURATION_MARKER, false, depth);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}
}
