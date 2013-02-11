/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.extended.ui;

import de.ovgu.featureide.fm.ui.AbstractUIPlugin;

import org.eclipse.swt.graphics.Image;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 * 
 *  @author Sebastian Henneberg
 */
public class EFMUIPlugin extends AbstractUIPlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.fm.extended.ui";

	private static EFMUIPlugin plugin;

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.plugin.AbstractUIPlugin#getID()
	 */
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
	public static EFMUIPlugin getDefault() {
		return plugin;
	}
	
	public static Image getImage(String name) {
		return getDefault().getImageDescriptor(
				"icons/" + name).createImage();
	}

}
