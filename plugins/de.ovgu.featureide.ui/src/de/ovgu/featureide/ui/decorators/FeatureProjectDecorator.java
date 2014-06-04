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
package de.ovgu.featureide.ui.decorators;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Adds a small overlay to projects belonging to FeatureIDE.
 * 
 * @author Tom Brosch
 */
public class FeatureProjectDecorator implements ILightweightLabelDecorator {

	private static final ImageDescriptor OVERLAY = UIPlugin.getDefault().getImageDescriptor("icons/FeatureProjectDecorator.png");

	public FeatureProjectDecorator() {
	}
	
	public void dispose() {
	}

	public void decorate(Object element, IDecoration decoration) {
		IProject project = (IProject) element;

		//decorate feature projects
		if (CorePlugin.hasProjectData(project)) {
			decoration.addOverlay(OVERLAY, IDecoration.TOP_LEFT);
		}
	}

	public void addListener(ILabelProviderListener listener) {
	}

	public void removeListener(ILabelProviderListener listener) {
	}

	public boolean isLabelProperty(Object element, String property) {
		return false;
	}
}
