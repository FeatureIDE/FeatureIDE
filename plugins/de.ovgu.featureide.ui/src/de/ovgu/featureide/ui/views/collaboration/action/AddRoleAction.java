/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.views.collaboration.action;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.ISafeRunnable;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;

/**
 * Add a role to the CollaborationDiagramm.
 * 
 * @author Constanze Adler
 * @author Stephan Besecke
 * @author Jens Meinicke
 */
public class AddRoleAction extends Action {
	private GraphicalViewerImpl viewer;
	
	private CollaborationView collaborationView;
	
	protected IStructuredSelection selection;
	
	public AddRoleAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView) {
		super(text);
		viewer = view;
		this.collaborationView = collaborationView;
	}
	
	public void setEnabled(boolean enable) {
		selection = (IStructuredSelection)viewer.getSelection();
		super.setEnabled(true);
	}
	
	public void run() {
		runExtension();
	}

	private void runExtension() {
		IConfigurationElement[] config = Platform.getExtensionRegistry()
			.getConfigurationElementsFor(UIPlugin.PLUGIN_ID + ".RunAddRoleAction");
		try {
			for (IConfigurationElement e : config) {
				if (e.getAttribute("composer").equals(collaborationView.getFeatureProject().getComposer().getName())) {
					final Object o = e.createExecutableExtension("class");
					if (o instanceof IRunAddRoleAction) {
						
						ISafeRunnable runnable = new ISafeRunnable() {
							@Override
							public void handleException(Throwable e) {
								UIPlugin.getDefault().logError(e);
							}
	
							@Override
							public void run() throws Exception {
								((IRunAddRoleAction) o).run(viewer, selection);
							}
						};
						SafeRunner.run(runnable);
					}
					break;
				}
			}
		} catch (CoreException ex) {
			UIPlugin.getDefault().logError(ex);
		}
	}
}
