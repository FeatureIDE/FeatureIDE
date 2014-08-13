package de.ovgu.featureide.munge_android;

import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.core.AbstractCorePlugin;

public class MungeAndroidCorePlugin extends AbstractCorePlugin {
	
	// The plug-in ID
	public static final String PLUGIN_ID = "de.ovgu.featureide.core.munge-android";

	// The shared instance
	private static MungeAndroidCorePlugin plugin;
	
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
	public static MungeAndroidCorePlugin getDefault() {
		return plugin;
	}

}
