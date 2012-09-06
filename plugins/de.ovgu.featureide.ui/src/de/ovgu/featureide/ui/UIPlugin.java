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
package de.ovgu.featureide.ui;

import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.PlatformUI;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.ui.AbstractUIPlugin;
import de.ovgu.featureide.ui.editors.JavaEditor;
import de.ovgu.featureide.ui.editors.annotation.EditorTracker;

/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author Marcus Leich
 * @author Thomas Thuem
 * @author Tom Brosch
 */
public class UIPlugin extends AbstractUIPlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.ui";

	private static UIPlugin plugin;

	private EditorTracker editorTracker;
	
	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		
		// XXX this is a bad workaround, but it seems to work pretty good
		PlatformUI.getWorkbench().getEditorRegistry().setDefaultEditor("*.java", JavaEditor.ID);
		
		editorTracker = new EditorTracker(PlatformUI.getWorkbench());
	}

	public void stop(BundleContext context) throws Exception {
		plugin = null;
		
		if (editorTracker != null) {
		    editorTracker.dispose();
		}
		
		super.stop(context);
	}

	public static UIPlugin getDefault() {
		return plugin;
	}

	public static Image getImage(String name) {
		return getDefault().getImageDescriptor("icons/" + name).createImage();
	}

}
