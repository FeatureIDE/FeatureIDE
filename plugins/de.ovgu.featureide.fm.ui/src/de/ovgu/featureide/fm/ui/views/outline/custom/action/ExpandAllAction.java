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
package de.ovgu.featureide.fm.ui.views.outline.custom.action;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Action which expands all elements in a treeviewer
 *
 * @author Christopher Sontag
 */
public class ExpandAllAction extends Action {

	private final TreeViewer viewer;

	/**
	 * Constructor for ExpandAllAction
	 *
	 * @param viewer
	 */
	public ExpandAllAction(TreeViewer viewer) {
		super();
		this.viewer = viewer;
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/expand.gif"));
	}

	@Override
	public void run() {
		viewer.expandAll();
		this.firePropertyChange("EXPAND", null, null);
	}

}
