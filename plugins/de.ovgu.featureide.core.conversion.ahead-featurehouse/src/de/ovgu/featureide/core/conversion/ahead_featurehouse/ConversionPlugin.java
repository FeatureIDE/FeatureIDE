package de.ovgu.featureide.core.conversion.ahead_featurehouse;

import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.ui.AbstractUIPlugin;

/**
 * The activator class controls the plug-in life cycle
 */
public class ConversionPlugin extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "de.ovgu.featureide.core.conversion.ahead-featurehouse"; //$NON-NLS-1$

	// The shared instance
	private static ConversionPlugin plugin;
	
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
	public static ConversionPlugin getDefault() {
		return plugin;
	}

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

}
