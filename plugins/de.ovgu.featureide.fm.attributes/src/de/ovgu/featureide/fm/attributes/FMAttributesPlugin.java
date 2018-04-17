package de.ovgu.featureide.fm.attributes;

import org.eclipse.swt.graphics.Image;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.attributes.format.XmlExtendedFeatureModelFormat;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * The activator class controls the plug-in life cycle
 */
public class FMAttributesPlugin extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "de.ovgu.featureide.fm.attributes"; //$NON-NLS-1$

	// The shared instance
	private static FMAttributesPlugin plugin;

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

		FMFactoryManager.factoryWorkspaceProvider.getFactoryWorkspace().assignID(XmlExtendedFeatureModelFormat.ID, ExtendedFeatureModelFactory.ID);

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
	public static FMAttributesPlugin getDefault() {
		return plugin;
	}

	public static Image getImage(String name) {
		return getDefault().getImageDescriptor("icons/" + name).createImage();
	}

}
