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
package de.ovgu.featureide.core.internal;

import org.eclipse.core.internal.resources.MarkerInfo;
import org.eclipse.core.internal.resources.Workspace;
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
@SuppressWarnings("restriction")
public class BuilderMarkerHandler implements IBuilderMarkerHandler {

	private static final String BUILDER_MARKER = CorePlugin.PLUGIN_ID + ".builderProblemMarker";

	private static final String CONFIGURATION_MARKER = CorePlugin.PLUGIN_ID + ".configurationProblemMarker";

	protected final IProject project;

	public BuilderMarkerHandler(IProject project) {
		this.project = project;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.core.internal.IMarkerHandler#createBuilderMarker(org .eclipse.core.resources.IResource, java.lang.String, int, int)
	 */
	@Override
	public void createBuilderMarker(IResource resource, String message, int lineNumber, int severity) {
		if (resource != null) {
			// for creating and deleting markers a synchronized file is
			// neccessary
			try {
				resource.refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (final CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		} else {
			resource = project;
		}

		// prevent duplicate error markers (e.g. caused by changing a jak file
		// that refines a non-valid jak file)
		deleteIfExists(resource, message, lineNumber, severity);

		try {
			final IMarker marker = resource.createMarker(BUILDER_MARKER);
			marker.setAttribute(IMarker.MESSAGE, message);
			marker.setAttribute(IMarker.SEVERITY, severity);
			marker.setAttribute(IMarker.LINE_NUMBER, lineNumber);
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	private void deleteIfExists(IResource resource, String message, int lineNumber, int severity) {
		try {
			if (!resource.exists()) {
				return;
			}
			final IMarker[] markers = resource.findMarkers(BUILDER_MARKER, false, IResource.DEPTH_ZERO);
			for (final IMarker marker : markers) {
				// XXX Workaround for possible null pointer exception at this point
				// TODO Fix cause of the null pointer or handle correctly
				try {
					if (marker.getAttribute(IMarker.MESSAGE).equals(message) && ((Integer) marker.getAttribute(IMarker.LINE_NUMBER) == lineNumber)
						&& ((Integer) marker.getAttribute(IMarker.SEVERITY) == severity)) {
						marker.delete();
					}
				} catch (final RuntimeException e) {}
			}
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.core.internal.IMarkerHandler#deleteBuilderMarkers( org.eclipse.core.resources.IResource, int)
	 */
	@Override
	public void deleteBuilderMarkers(IResource resource, int depth) {
		if ((resource != null) && resource.exists()) {
			try {
				resource.deleteMarkers(BUILDER_MARKER, false, depth);
			} catch (final CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		}
	}

	public void createConfigurationMarker(IResource resource, String message, int lineNumber, int severity) {
		if (hasMarker(resource, message, lineNumber)) {
			return;
		}
		try {
			final IMarker marker = resource.createMarker(CONFIGURATION_MARKER);
			final MarkerInfo info = ((Workspace) resource.getWorkspace()).getMarkerManager().findMarkerInfo(resource, marker.getId());
			if (marker.exists() && (info != null)) {
				marker.setAttribute(IMarker.MESSAGE, message);
				marker.setAttribute(IMarker.SEVERITY, severity);
				marker.setAttribute(IMarker.LINE_NUMBER, lineNumber);
			} else {
				System.err.println(info);
			}
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * @param resource
	 * @param message
	 * @param lineNumber
	 * @return
	 */
	private boolean hasMarker(final IResource resource, final String message, final int lineNumber) {
		try {
			final IMarker[] marker = resource.findMarkers(CONFIGURATION_MARKER, false, IResource.DEPTH_ZERO);
			if (marker != null) {
				for (final IMarker m : marker) {
					if (m != null) {
						final Object markerMessage = m.getAttribute(IMarker.MESSAGE);
						final Object markerLine = m.getAttribute(IMarker.LINE_NUMBER);
						if ((markerMessage != null) && markerMessage.equals(message) && (markerLine != null) && markerLine.equals(lineNumber)) {
							return true;
						}
					}
				}
			}
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return false;
	}

	public void deleteConfigurationMarkers(IResource resource, int depth) {
		try {
			resource.deleteMarkers(CONFIGURATION_MARKER, false, depth);
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}
}
