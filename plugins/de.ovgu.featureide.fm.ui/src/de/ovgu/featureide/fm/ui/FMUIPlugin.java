/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.ui;

import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.swt.graphics.Image;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.core.io.ExternalChangeListener;
import de.ovgu.featureide.fm.ui.editors.EclipseExternalChangeListener;

/**
 * The activator class controls the plug-in life cycle.
 *
 * @author Christian Kaestner
 * @author Thomas Thuem
 */
public class FMUIPlugin extends AbstractUIPlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.fm.ui";

	private static FMUIPlugin plugin;

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		final EclipseExternalChangeListener eclipseExternalChangeListener = new EclipseExternalChangeListener();
		ExternalChangeListener.listener = eclipseExternalChangeListener;
		ResourcesPlugin.getWorkspace().addResourceChangeListener(eclipseExternalChangeListener);
	}

	@Override
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
		final ExternalChangeListener listener = ExternalChangeListener.listener;
		if (listener instanceof IResourceChangeListener) {
			ResourcesPlugin.getWorkspace().removeResourceChangeListener((IResourceChangeListener) listener);
		}
	}

	public static FMUIPlugin getDefault() {
		return plugin;
	}

	public static Image getImage(String name) {
		return getDefault().getImageDescriptor("icons/" + name).createImage();
	}

}
