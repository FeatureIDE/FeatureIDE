/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.REVERSE_LAYOUT_ORDER;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.event.FeatureModelEvent;
import de.ovgu.featureide.fm.core.base.event.PropertyConstants;
import de.ovgu.featureide.fm.core.base.util.tree.TreeOperations;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation with functionality to reverse the feature model layout order.
 * Enables undo/redo functionality.
 * 
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class ModelReverseOrderOperation extends AbstractGraphicalFeatureModelOperation {

	private static final String LABEL = REVERSE_LAYOUT_ORDER;

	public ModelReverseOrderOperation(IGraphicalFeatureModel featureModel) {
		super(featureModel, LABEL);
		setEventId(PropertyConstants.MODEL_DATA_LOADED);
	}

	@Override
	protected FeatureModelEvent internalRedo() {
		final IGraphicalFeature root = graphicalFeatureModel.getFeatures().getObject();
		TreeOperations.reverse(root.getTree());
		if (!graphicalFeatureModel.getLayout().hasFeaturesAutoLayout()) {
			Point mid = FeatureUIHelper.getLocation(root).getCopy();
			mid.x += FeatureUIHelper.getSize(root).width / 2;
			mid.y += FeatureUIHelper.getSize(root).height / 2;
			mirrorFeaturePositions(root, mid, FeatureUIHelper.hasVerticalLayout(graphicalFeatureModel));
		}
		return null;
	}

	private void mirrorFeaturePositions(IGraphicalFeature feature, Point mid, boolean vertical) {
		if (!feature.getTree().isRoot()) {
			Point featureMid = FeatureUIHelper.getLocation(feature).getCopy();
			Dimension size = FeatureUIHelper.getSize(feature).getCopy();

			if (vertical) {
				featureMid.y += size.height / 2;
				featureMid.y = 2 * mid.y - featureMid.y;
				featureMid.y -= size.height / 2;
			} else {
				featureMid.x += size.width / 2;
				featureMid.x = 2 * mid.x - featureMid.x;
				featureMid.x -= size.width / 2;
			}

			FeatureUIHelper.setLocation(feature, featureMid);
		}
		if (feature.getTree().hasChildren()) {
			for (IGraphicalFeature child : feature.getTree().getChildrenObjects()) {
				mirrorFeaturePositions(child, mid, vertical);
			}
		}
	}

	@Override
	protected FeatureModelEvent internalUndo() {
		return internalRedo();
	}

}
