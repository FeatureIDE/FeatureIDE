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
package de.ovgu.featureide.ui.decorators;

import java.net.URL;
import java.util.LinkedList;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.listeners.IFeatureFolderListener;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Adds the delete icon to feature folder if the folder corresponds to an abstract feature.
 */
public class FeatureFolderDecorator implements ILightweightLabelDecorator, IFeatureFolderListener {

	private static final ImageDescriptor OVERLAY;

	static {
		final URL url = UIPlugin.getDefault().getBundle().getEntry("/icons/deleted.gif");
		OVERLAY = ImageDescriptor.createFromURL(url);
	}

	private final LinkedList<ILabelProviderListener> listenerList = new LinkedList<ILabelProviderListener>();

	public FeatureFolderDecorator() {
		CorePlugin.getDefault().addFeatureFolderListener(this);
	}

	@Override
	public void dispose() {
		CorePlugin.getDefault().removeFeatureFolderListener(this);
	}

	@Override
	public void decorate(Object element, IDecoration decoration) {
		final IFolder folder = (IFolder) element;

		// decorate only files in our projects
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(folder);
		if (featureProject == null) {
			return;
		}

		final IComposerExtensionClass composer = featureProject.getComposer();
		if ((composer == null) || !composer.hasFeatureFolder()) {
			return;
		}
		if (!featureProject.getSourceFolder().equals(folder.getParent())) {
			return;
		}

		// handle only not-in-use folders
		final IFeature feature = featureProject.getFeatureModel().getFeature(folder.getName());
		if ((feature == null) || feature.getStructure().isAbstract()) {
			// decorate not-in-use folders
			decoration.addOverlay(OVERLAY, IDecoration.TOP_LEFT);
		}
	}

	@Override
	public void addListener(ILabelProviderListener listener) {
		if (!listenerList.contains(listener)) {
			listenerList.add(listener);
		}
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {
		listenerList.remove(listener);
	}

	@Override
	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	@Override
	public void featureFolderChanged(IFolder folder) {
		final LabelProviderChangedEvent event = new LabelProviderChangedEvent(this, folder);
		for (final ILabelProviderListener listener : listenerList) {
			listener.labelProviderChanged(event);
		}
	}

}
