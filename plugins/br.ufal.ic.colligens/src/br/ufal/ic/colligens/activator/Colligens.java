package br.ufal.ic.colligens.activator;

import java.io.File;
import java.net.URL;

import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.osgi.service.datalocation.Location;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.ui.AbstractUIPlugin;

/**
 * The activator class controls the plug-in life cycle
 */
/**
 *
 *
 * @author Dalton
 *
 *
 *
 **/

public class Colligens extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "br.ufal.ic.colligens"; //$NON-NLS-1$
	public static final String PLUGIN_NAME = "Colligens";

	// The shared instance
	private static Colligens plugin;

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext )
	 */
	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;

		final Start inicialize = new Start();
		inicialize.SystemClear();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext )
	 */
	@Override
	public void stop(BundleContext context) throws Exception {
		final Start inicialize = new Start();
		inicialize.SystemClear();

		plugin = null;
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static Colligens getDefault() {
		return plugin;
	}

	/**
	 * Returns an image descriptor for the image file at the given plug-in relative path
	 *
	 * @param path the path
	 * @return the image descriptor
	 */
	@Override
	public ImageDescriptor getImageDescriptor(String path) {
		return imageDescriptorFromPlugin(PLUGIN_ID, path);
	}

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	/**
	 * Returns the configuration directory
	 *
	 *
	 * @return directory configuration
	 */
	public File getConfigDir() {
		final Location location = Platform.getConfigurationLocation();
		File file = null;
		if (location != null) {
			final URL configURL = location.getURL();
			if ((configURL != null) && configURL.getProtocol().startsWith("file")) {
				file = new File(configURL.getFile(), PLUGIN_ID);
				file.mkdirs();
				return file;
			}
		}
		file = getStateLocation().toFile();
		file.mkdirs();
		return file;
	}

}
