/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.attributes;

import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.core.init.LibraryManager;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;

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

	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		LibraryManager.registerLibrary(FMAttributesEclipseLibrary.getInstance());

		IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		page.addPartListener(new IPartListener() {

			@Override
			public void partOpened(IWorkbenchPart part) {
				if (part instanceof FeatureModelEditor) {
					try {
						page.showView("de.ovgu.featureide.fm.attributes.view.FeatureAttributeView");
					} catch (PartInitException e) {
						e.printStackTrace();
					}
				}
			}

			@Override
			public void partDeactivated(IWorkbenchPart part) {

			}

			@Override
			public void partClosed(IWorkbenchPart part) {

			}

			@Override
			public void partBroughtToTop(IWorkbenchPart part) {

			}

			@Override
			public void partActivated(IWorkbenchPart part) {

			}
		});
	}

	public void stop(BundleContext context) throws Exception {
		LibraryManager.deregisterLibrary(FMAttributesEclipseLibrary.getInstance());
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
