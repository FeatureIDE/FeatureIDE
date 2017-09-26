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

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.listeners.ICurrentConfigurationListener;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * A decorator that marks the configuration files that is selected for building.
 *
 * @author Marcus Leich
 */
public class ActiveConfigurationDecorator implements ILightweightLabelDecorator, ICurrentConfigurationListener {

	private final ImageDescriptor icon;
	private final LinkedList<ILabelProviderListener> listeners;

	public ActiveConfigurationDecorator() {
		final URL url = de.ovgu.featureide.ui.UIPlugin.getDefault().getBundle().getEntry("/icons/currentconfiguration.gif");
		icon = ImageDescriptor.createFromURL(url);
		listeners = new LinkedList<ILabelProviderListener>();

		// add Listener to Activator
		de.ovgu.featureide.core.CorePlugin.getDefault().addCurrentConfigurationListener(this);
	}

	@Override
	public void decorate(Object element, IDecoration decoration) {
		final IFeatureProject pd = CorePlugin.getFeatureProject((IResource) element);
		if ((pd != null) && ((IResource) element).equals(pd.getCurrentConfiguration())) {
			decoration.addOverlay(icon, IDecoration.TOP_LEFT);
		}
	}

	@Override
	public void addListener(ILabelProviderListener listener) {
		if (!listeners.contains(listener)) {
			listeners.add(listener);
		}
	}

	@Override
	public void dispose() {
		de.ovgu.featureide.core.CorePlugin.getDefault().removeCurrentConfigurationListener(this);
	}

	private void refresh(IResource[] res) {
		final LabelProviderChangedEvent e = new LabelProviderChangedEvent(this, res);
		for (final ILabelProviderListener l : listeners) {
			l.labelProviderChanged(e);
		}
	}

	@Override
	public boolean isLabelProperty(Object element, String property) {
		// this is not a property dependant label
		return false;
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {
		listeners.remove(listener);
	}

	@Override
	public void currentConfigurationChanged(IFeatureProject data) {
		try {
			refresh(data.getConfigFolder().members());
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
	}

}
