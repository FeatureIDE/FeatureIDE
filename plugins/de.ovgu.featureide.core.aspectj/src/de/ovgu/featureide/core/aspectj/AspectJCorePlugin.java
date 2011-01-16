package de.ovgu.featureide.core.aspectj;

import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.core.AbstractCorePlugin;

/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author Jens Meinicke
 */
public class AspectJCorePlugin extends AbstractCorePlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "de.ovgu.featureide.core.aspectj"; //$NON-NLS-1$

	// The shared instance
	private static AspectJCorePlugin plugin;

	public AspectJCorePlugin() {	
	}

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
	public static AspectJCorePlugin getDefault() {
		return plugin;
	}

}
