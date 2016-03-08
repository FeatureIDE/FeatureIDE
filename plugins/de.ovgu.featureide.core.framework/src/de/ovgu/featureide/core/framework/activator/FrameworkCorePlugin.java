package de.ovgu.featureide.core.framework.activator;

import org.osgi.framework.BundleContext;
import de.ovgu.featureide.fm.core.AbstractCorePlugin;

/**
 * Framework plugin
 * 
 * @author Daniel Hohmann
 *
 */
public class FrameworkCorePlugin extends AbstractCorePlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.core.framework";

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	private static FrameworkCorePlugin plugin;

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
	public static FrameworkCorePlugin getDefault() {
		return plugin;
	}

}
