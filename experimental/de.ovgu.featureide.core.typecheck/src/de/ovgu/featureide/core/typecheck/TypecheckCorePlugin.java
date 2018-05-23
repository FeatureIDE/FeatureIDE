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
package de.ovgu.featureide.core.typecheck;

import java.util.Arrays;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.AbstractCorePlugin;

public class TypecheckCorePlugin extends AbstractCorePlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.core.typecheck";

	private static final String CHECK_MARKER = PLUGIN_ID + ".checkMarker";
	
	private static final String[] supportedComposers = { "de.ovgu.featureide.composer.featurehouse" };
	static {
		Arrays.sort(supportedComposers);
	}
	
	private static TypecheckCorePlugin plugin;
	
	public static boolean isSupportedComposer(String composerID) {
		return Arrays.binarySearch(TypecheckCorePlugin.supportedComposers, composerID) >= 0;
	}

	@Override
	public String getID() {
		return PLUGIN_ID;
	}
	
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
	}
	
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	public static TypecheckCorePlugin getDefault() {
		return plugin;
	}

	public void logln(String message) {
		if (getDefault().isDebugging()) {
			System.out.println(message);
		}
	}

	public void clearMarkers(IResource res) {
		if (res instanceof IFile) {
			deleteMarkers(res, IResource.DEPTH_INFINITE);
		} else if (res instanceof IFolder) {
			try {
				for (IResource r : ((IFolder) res).members()) {
					clearMarkers(r);
				}
			} catch (CoreException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}

	public void createMarker(IResource resource, String message, int lineNumber, int severity) {
		if (resource != null) {
			// for creating and deleting markers a synchronized file is
			// neccessary
			try {
				resource.refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (CoreException e) {
				TypecheckCorePlugin.getDefault().logError(e);
			}
		} else
			return;

		// prevent duplicate error markers (e.g. caused by changing a jak file
		// that refines a non-valid jak file)
		deleteIfExists(resource, message, lineNumber, severity);

		try {
			IMarker marker = resource.createMarker(CHECK_MARKER);
			marker.setAttribute(IMarker.MESSAGE, message);
			marker.setAttribute(IMarker.SEVERITY, severity);
			marker.setAttribute(IMarker.LINE_NUMBER, lineNumber);
		} catch (CoreException e) {
			TypecheckCorePlugin.getDefault().logError(e);
		}
	}

	private void deleteIfExists(IResource resource, String message, int lineNumber, int severity) {
		try {
			IMarker[] markers = resource.findMarkers(CHECK_MARKER, false, IResource.DEPTH_ZERO);
			if (!resource.exists())
				return;
			for (IMarker marker : markers) {
				if (marker.getAttribute(IMarker.MESSAGE).equals(message) && (Integer) marker.getAttribute(IMarker.LINE_NUMBER) == lineNumber && (Integer) marker.getAttribute(IMarker.SEVERITY) == severity) {
					marker.delete();
				}
			}
		} catch (CoreException e) {
			TypecheckCorePlugin.getDefault().logError(e);
		}
	}

	public void deleteMarkers(IResource resource, int depth) {
		if (resource != null && resource.exists()) {
			try {
				resource.deleteMarkers(CHECK_MARKER, false, depth);
			} catch (CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		}
	}
}
