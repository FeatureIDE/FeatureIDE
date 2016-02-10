package de.ovgu.featureide.featuremake;

import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.core.AbstractCorePlugin;

public class FeatureMakeCorePlugin extends AbstractCorePlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.composer.featuremake";
	private static FeatureMakeCorePlugin plugin;

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.osgi.framework.BundleActivator#start(org.osgi.framework.
	 * BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.osgi.framework.BundleActivator#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	public static FeatureMakeCorePlugin getDefault() {
		return plugin;
	}

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

}
