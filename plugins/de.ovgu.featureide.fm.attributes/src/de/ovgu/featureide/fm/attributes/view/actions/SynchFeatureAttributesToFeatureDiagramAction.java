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
package de.ovgu.featureide.fm.attributes.view.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeViewSelectionFilter;

/**
 * Action for the {@link FeatureAttributeView}. Is used to toggle the filtering for the view.
 * 
 * @see FeatureAttributeViewSelectionFilter
 * 
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class SynchFeatureAttributesToFeatureDiagramAction extends Action {

	private FeatureAttributeView view;
	private TreeViewer treeView;

	public SynchFeatureAttributesToFeatureDiagramAction(FeatureAttributeView view, TreeViewer treeView, ImageDescriptor icon) {
		super("", icon);
		this.view = view;
		this.treeView = treeView;
		setChecked(view.synchToFeatureDiagram);
	}

	@Override
	public void run() {
		view.synchToFeatureDiagram = !view.synchToFeatureDiagram;
		setChecked(view.synchToFeatureDiagram);
		view.selectedAutomaticFeatures = null;
		view.selectedManualFeatures = null;
		treeView.refresh();
	}

}
