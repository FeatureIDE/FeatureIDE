package de.ovgu.featureide.ui.android;

import de.ovgu.featureide.fm.ui.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 * 
 * @author Lars-Christian Schulz
 * @author Eric Guimatsia
 */
public class AndroidUIPlugin extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "de.ovgu.featureide.ui.android"; //$NON-NLS-1$

	// The shared instance
	private static AndroidUIPlugin plugin;
	
	/**
	 * The constructor
	 */
	public AndroidUIPlugin() {
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

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static AndroidUIPlugin getDefault() {
		return plugin;
	}
}
