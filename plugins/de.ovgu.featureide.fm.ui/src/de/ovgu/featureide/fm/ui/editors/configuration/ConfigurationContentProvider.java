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
package de.ovgu.featureide.fm.ui.editors.configuration;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.TreeElement;


/**
 * Converts a given configuration into elements of an tree viewer.
 * 
 * @author Thomas Thuem
 */
public class ConfigurationContentProvider implements
		IStructuredContentProvider, ITreeContentProvider {

	private Configuration configuration;

	public void inputChanged(Viewer v, Object oldInput, Object newInput) {
		configuration = (Configuration) newInput;
	}

	public void dispose() {
	}
	
	public Object[] getElements(Object parent) {
		if (parent == null)
			return new String[] { "Loading..." };
		if (parent == configuration)
			return new Object[] { configuration.getRoot() };
		return getChildren(parent);
	}

	public Object getParent(Object child) {
		if (child instanceof TreeElement)
			return ((TreeElement) child).getParent();
		return null;
	}

	public Object[] getChildren(Object parent) {
		if (parent instanceof TreeElement)
			return ((TreeElement) parent).getChildren();
		return new Object[0];
	}

	public boolean hasChildren(Object parent) {
		if (parent instanceof TreeElement)
			return ((TreeElement) parent).hasChildren();
		return false;
	}

}
