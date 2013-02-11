package de.ovgu.featureide.core.typecheck;

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

    public static String[] supportedComposers = { "de.ovgu.featureide.composer.featurehouse" };

    private static TypecheckCorePlugin plugin;

    @Override
    public String getID() {
	return PLUGIN_ID;
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext
     * )
     */
    public void start(BundleContext context) throws Exception {
	super.start(context);
	plugin = this;
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext
     * )
     */
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
    
    public void createMarker(IResource resource, String message,
	    int lineNumber, int severity) {
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

    private void deleteIfExists(IResource resource, String message,
	    int lineNumber, int severity) {
	try {
	    IMarker[] markers = resource.findMarkers(CHECK_MARKER, false,
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
