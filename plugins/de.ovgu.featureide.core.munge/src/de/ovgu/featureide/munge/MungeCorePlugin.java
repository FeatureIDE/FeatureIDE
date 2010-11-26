package de.ovgu.featureide.munge;

import de.ovgu.featureide.fm.core.AbstractCorePlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 * 
 * @author Jens Meinicke
 */
public class MungeCorePlugin extends AbstractCorePlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "de.ovgu.featureide.core.munge"; //$NON-NLS-1$

	// The shared instance
	private static MungeCorePlugin plugin;
	
	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static MungeCorePlugin getDefault() {
		return plugin;
	}

}
