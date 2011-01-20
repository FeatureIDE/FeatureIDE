/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import java.util.LinkedList;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Changes the order of children for every feature.
 * 
 * @author Thomas Thuem
 */
public class ReverseOrderAction extends Action {

	public static String ID = "de.ovgu.featureide.reverseorder";

	private final FeatureModel featureModel;
	
	public ReverseOrderAction(GraphicalViewerImpl viewer, FeatureModel featureModel) {
		super("Reverse Order");
		this.featureModel = featureModel;
	}

	@Override
	public void run() {
		reverse(featureModel.getRoot());
		featureModel.handleModelDataChanged();
	}

	private void reverse(Feature feature) {
		LinkedList<Feature> children = feature.getChildren();
		for (int i = 0; i < children.size() - 1; i++)
			children.add(i,children.removeLast());
		for (Feature child : feature.getChildren())
			reverse(child);
	}

}
