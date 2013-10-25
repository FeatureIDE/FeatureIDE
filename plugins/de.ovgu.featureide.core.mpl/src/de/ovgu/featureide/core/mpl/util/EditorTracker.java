/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.mpl.util;

import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.IWindowListener;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;

/**
 * Listen for the {@link ConfigurationEditor} and attach an {@link IPropertyListener}.
 * 
 * @author Sebastian Krieter
 */
public class EditorTracker {
	private static EditorTracker instance;
	
	private final IWindowListener windowListener = new IWindowListener() {
		@Override
		public void windowOpened(IWorkbenchWindow window) {
			window.getPartService().addPartListener(partListener);
		}

		@Override
		public void windowClosed(IWorkbenchWindow window) {
			window.getPartService().removePartListener(partListener);
		}

		public void windowActivated(IWorkbenchWindow window) {}
		public void windowDeactivated(IWorkbenchWindow window) {}
	};

	private final IPartListener2 partListener = new IPartListener2() {
		@Override
		public void partActivated(IWorkbenchPartReference partref) {
			if (partref.getId().equals(ConfigurationEditor.ID)) {
				attachListener(partref);
			}
		}

		public void partOpened(IWorkbenchPartReference partref) {}
		public void partBroughtToTop(IWorkbenchPartReference partref) {}
		public void partVisible(IWorkbenchPartReference partref) {}
		public void partInputChanged(IWorkbenchPartReference partref) {}
		public void partClosed(IWorkbenchPartReference partref) {}
		public void partDeactivated(IWorkbenchPartReference partref) {}
		public void partHidden(IWorkbenchPartReference partref) {}
	};
	
	private final IPropertyListener propertyListener;
	
	private void attachListener(IWorkbenchPartReference partref) {
		IWorkbenchPart part = partref.getPart(true);
		if (part instanceof ConfigurationEditor) {
			ConfigurationEditor confEditor = (ConfigurationEditor) partref.getPart(true);
			if (MPLPlugin.getDefault().isInterfaceProject(confEditor.file.getProject())) {
				confEditor.addPropertyListener(propertyListener);
			}
		}
	}
	
	public static void init(IPropertyListener propertyListener) {
		if (instance == null) {
			instance = new EditorTracker(propertyListener);
		}
	}
	
	private EditorTracker(IPropertyListener propertyListener) {
		this.propertyListener = propertyListener;
		IWorkbench workbench = PlatformUI.getWorkbench();
		for (final IWorkbenchWindow w : workbench.getWorkbenchWindows()) {
			w.getPartService().addPartListener(partListener);
		}
		workbench.addWindowListener(windowListener);
	}

	public static void dispose() {
		IWorkbench workbench = PlatformUI.getWorkbench();
		workbench.removeWindowListener(instance.windowListener);
		for (final IWorkbenchWindow w : workbench.getWorkbenchWindows()) {
			w.getPartService().removePartListener(instance.partListener);
		}
		instance = null;
	}
}