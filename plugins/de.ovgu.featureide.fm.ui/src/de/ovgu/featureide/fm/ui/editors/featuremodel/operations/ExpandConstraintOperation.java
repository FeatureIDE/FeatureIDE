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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.FOCUS_ON_CONTAINED_FEATURES;

import java.util.LinkedList;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation with functionality to expand only features of this constraint. Enables undo/redo functionality. Enables undo/redo functionality.
 *
 * @author Maximilian K�hl
 * @author Christopher Sontag
 */
public class ExpandConstraintOperation extends AbstractGraphicalFeatureModelOperation {

	private final int constraintIndex;
	private final LinkedList<IGraphicalFeature> affectedFeatureList = new LinkedList<>();

	public ExpandConstraintOperation(IGraphicalFeatureModel graphicalFeatureModel, IConstraint constraint) {
		super(graphicalFeatureModel, FOCUS_ON_CONTAINED_FEATURES);
		constraintIndex = featureModelManager.editObject().getConstraintIndex(constraint);
	}

	public void expandParents(IFeature feature) {
		if (feature.getStructure().isRoot()) {
			return;
		}

		IFeatureStructure p = feature.getStructure().getParent();
		IGraphicalFeature g = null;
		while (!p.isRoot()) {
			g = graphicalFeatureModel.getGraphicalFeature(p.getFeature());
			if (g.isCollapsed()) {
				expandFeature(g);
			}
			p = p.getParent();
		}
		if (g != null) {
			g.setCollapsed(false);
		}
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IConstraint constraint = featureModel.getConstraints().get(constraintIndex);
		getCollapsedFeatures();
		final CollapseAllOperation collapseAll = new CollapseAllOperation(graphicalFeatureModel, true);

		// execute directly and push not in operation history otherwise no more than one undo possible
		collapseAll.operation(featureModel);

		for (final IFeature feature : constraint.getContainedFeatures()) {
			expandParents(feature);
		}

		return new FeatureIDEEvent(featureModel.getStructure().getRoot().getFeature(), EventType.COLLAPSED_ALL_CHANGED, null, constraint);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IConstraint constraint = featureModel.getConstraints().get(constraintIndex);
		final CollapseAllOperation collapseAll = new CollapseAllOperation(graphicalFeatureModel, true);

		// execute directly and push not in operation history otherwise no more than one undo possible
		collapseAll.operation(featureModel);
		for (final IGraphicalFeature f : affectedFeatureList) {
			expandFeature(f);
		}
		return new FeatureIDEEvent(featureModel.getStructure().getRoot().getFeature(), EventType.COLLAPSED_ALL_CHANGED, null, constraint);
	}

	/**
	 * Collects all features that are not collapsed from the featureModel.
	 */
	private void getCollapsedFeatures() {
		affectedFeatureList.clear();
		for (final IGraphicalFeature f : graphicalFeatureModel.getFeatures()) {
			if (!f.isCollapsed()) {
				affectedFeatureList.add(f);
			}
		}
	}

	/**
	 * Expands a single feature.
	 *
	 * @param featureStructure
	 */
	private void expandFeature(IGraphicalFeature feature) {
		feature.setCollapsed(false);
	}
}
