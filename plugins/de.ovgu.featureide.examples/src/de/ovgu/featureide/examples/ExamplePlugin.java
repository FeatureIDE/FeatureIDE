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
package de.ovgu.featureide.examples;

import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.ui.AbstractUIPlugin;

/**
 * The activator class controls the plug-in life cycle.
 *
 * @author Thomas Thuem
 * @author Jens Meinicke
 */
public class ExamplePlugin extends AbstractUIPlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.examples";

	private static ExamplePlugin plugin;

	public static final String FeatureIDE_EXAMPLE_DIR = "featureide_examples";//$NON-NLS-1$
	public static final String FeatureIDE_EXAMPLE_INDEX = "projects.xml";//$NON-NLS-1$

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		new Thread() {

			@Override
			public void run() {
				try {
					ClassLoader.getSystemClassLoader().loadClass("de.ovgu.featureide.examples.wizards.ProjectProvider");
				} catch (final ClassNotFoundException e) {
					ExamplePlugin.getDefault().logError(e);
				}
			};
		}.start();
	}

	@Override
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	public static ExamplePlugin getDefault() {
		return plugin;
	}

}
