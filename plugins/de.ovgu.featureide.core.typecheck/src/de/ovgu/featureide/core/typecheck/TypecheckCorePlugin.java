package de.ovgu.featureide.core.typecheck;

import org.osgi.framework.BundleContext;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.AbstractCorePlugin;


public class TypecheckCorePlugin extends AbstractCorePlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.core.typecheck";

	private static TypecheckCorePlugin plugin;
	
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

	public static TypecheckCorePlugin getDefault() {
		return plugin;
	}
}
