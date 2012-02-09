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
package de.ovgu.featureide.ui.decorators;

import java.util.LinkedList;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.listeners.IFeatureFolderListener;
import de.ovgu.featureide.ui.UIPlugin;


public class FeatureFolderDecorator implements ILightweightLabelDecorator, IFeatureFolderListener {
	
	private static final ImageDescriptor OVERLAY = UIPlugin.getDefault().getImageDescriptor("deleted.gif");

	private final LinkedList<ILabelProviderListener> listenerList = new LinkedList<ILabelProviderListener>();
	
	public FeatureFolderDecorator() {
		de.ovgu.featureide.core.CorePlugin.getDefault().addFeatureFolderListener(this);
	}
	
	public void dispose() {
		de.ovgu.featureide.core.CorePlugin.getDefault().removeFeatureFolderListener(this);
	}

	public void decorate(Object element, IDecoration decoration) {
		IFolder folder = (IFolder) element;

		//decorate only files in our projects
		IFeatureProject featureProject = CorePlugin.getFeatureProject(folder);
		if (featureProject == null || featureProject.getSourceFolder() == null || 
				!featureProject.getSourceFolder().equals(folder.getParent()))
			return;
		
		//handle only not-in-use folders
		if (featureProject.getFeatureModel().containsLayer(folder.getName()))
			return;

		//decorate non-empty not-in-use folders
		decoration.addOverlay(OVERLAY, IDecoration.TOP_LEFT);
	}

	public void addListener(ILabelProviderListener listener) {
		if (!listenerList.contains(listener))
			listenerList.add(listener);
	}

	public void removeListener(ILabelProviderListener listener) {
		listenerList.remove(listener);
	}

	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.core.listeners.IFeatureFolderListener#featureFolderChanged(org.eclipse.core.resources.IFolder)
	 */
	public void featureFolderChanged(IFolder folder) {
		LabelProviderChangedEvent event = new LabelProviderChangedEvent(this, folder);
		for (ILabelProviderListener listener : listenerList) 
			listener.labelProviderChanged(event);
	}

}
