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
package de.ovgu.featureide.fm.ui.views.constraintview.listener;

import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeSelection;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.FeatureFigure;
import de.ovgu.featureide.fm.ui.utils.FeatureModelUtil;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;

/**
 * ConstraintViewSelectionChangedListener
 *
 * @author "Rosiak Kamil"
 */
public class ConstraintViewSelectionChangedListener implements ISelectionChangedListener {
	private final ConstraintViewController controller;

	public ConstraintViewSelectionChangedListener(ConstraintViewController controller) {
		this.controller = controller;
	}

	@Override
	public void selectionChanged(SelectionChangedEvent event) {
		final TreeSelection treeSelection = (TreeSelection) event.getSelection();
		final IConstraint constraint = (IConstraint) treeSelection.getFirstElement();
		if (FeatureModelUtil.getActiveFMEditor() != null) {
			controller.setRefreshWithDelete(false);
			if (constraint != null) {
				FeatureModelUtil.getActiveFMEditor().diagramEditor.setActiveExplanation(constraint.getFeatureModel().getAnalyser().getExplanation(constraint));
			}
			for (final IFeature feature : FeatureModelUtil.getFeatureModel().getFeatures()) {
				final IGraphicalFeature graphFeature =
					FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().getGraphicalFeature(feature);
				final IGraphicalFeatureModel graphModel = FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel();
				if ((constraint != null) && constraint.getContainedFeatures().contains(feature)) {
					graphFeature.setConstraintSelected(true);
				} else {
					graphFeature.setConstraintSelected(false);
				}
				new FeatureFigure(graphFeature, graphModel).setProperties();
			}
		}
	}

}
