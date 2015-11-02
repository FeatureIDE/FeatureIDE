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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import static de.ovgu.featureide.fm.core.localization.StringTable.MANUAL_LAYOUT;

import java.util.LinkedList;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * A helper class for the feature diagram layout.
 * 
 * @author David Halm
 * @author Patrick Sulkowski
 */
public class FeatureDiagramLayoutHelper {

	/**
	 * returns label texts (e.g. for the context menu)
	 */
	public static String getLayoutLabel(int layoutAlgorithmNum) {
		switch (layoutAlgorithmNum) {
		case 0:
			return MANUAL_LAYOUT;
		case 1:
			return "Top-Down (ordered)";
		case 2:
			return "Top-Down (centered)";
		case 3:
			return "Top-Down (left-aligned)";
		case 4:
			return "Left To Right (ordered)";
		case 5:
			return "Left To Right (curved)";
		default:
			return "Top-Down (ordered)";
		}
	}

	/**
	 * sets initial positions for new constraints
	 * needed for manual layout
	 */
	public static void initializeConstraintPosition(IGraphicalFeatureModel featureModel, int index) {
		Point newLocation = new Point(0, 0);
		IGraphicalConstraint constraint = featureModel.getConstraints().get(index);
		int leftX = Integer.MAX_VALUE;
		int rightX = Integer.MIN_VALUE;
		final int constraintCount = featureModel.getConstraints().size();
		if (constraintCount == 1) {
			for (IGraphicalFeature feature : featureModel.getFeatures()) {
				if (FeatureUIHelper.getLocation(feature).y > newLocation.y) {
					newLocation.y = FeatureUIHelper.getLocation(feature).y;
				}
				if (FeatureUIHelper.getLocation(feature).x > rightX) {
					rightX = FeatureUIHelper.getLocation(feature).x;
				}
				if (FeatureUIHelper.getLocation(feature).x < leftX) {
					leftX = FeatureUIHelper.getLocation(feature).x;
				}
			}
			newLocation.x = (leftX + rightX) / 2;
			newLocation.y += FMPropertyManager.getFeatureSpaceY();
		} else {
			IGraphicalConstraint lastConstraint = featureModel.getConstraints().get(constraintCount - 2);
			newLocation = FeatureUIHelper.getLocation(lastConstraint).getCopy();
			newLocation.y += FMPropertyManager.getConstraintSpace();
		}
		FeatureUIHelper.setLocation(constraint, newLocation);
	}

	/**
	 * sets initial positions for new features (above)
	 * needed for manual layout
	 */
	public static void initializeCompoundFeaturePosition(IGraphicalFeatureModel featureModel, LinkedList<IGraphicalFeature> selectedFeatures, IGraphicalFeature newCompound) {
		Point initPos = new Point(0, 0);
		int xAcc = 0;
		for (IGraphicalFeature feature : selectedFeatures) {
			if (initPos.y < FeatureUIHelper.getLocation(feature).y) {
				initPos.y = FeatureUIHelper.getLocation(feature).y;
			}
			xAcc += FeatureUIHelper.getLocation(feature).x;
		}
		initPos.x = (xAcc / selectedFeatures.size());
		if (newCompound.getObject().getStructure().isRoot()) {
			initPos.y = (initPos.y - FMPropertyManager.getFeatureSpaceY());
		} else {
			IGraphicalFeature parent = newCompound.getTree().getParentObject();
			initPos.y = (initPos.y + FeatureUIHelper.getLocation(parent).y) / 2;
			initPos.x = (initPos.x + FeatureUIHelper.getLocation(parent).x) / 2;
		}
		FeatureUIHelper.setLocation(newCompound, initPos);

	}

	/**
	 * sets initial positions for new features (below)
	 * needed for manual layout
	 */
	public static void initializeLayerFeaturePosition(IGraphicalFeatureModel featureModel, IGraphicalFeature newLayer, IGraphicalFeature feature) {
		if (!FeatureUIHelper.hasVerticalLayout(featureModel)) {
			Point initPos = FeatureUIHelper.getLocation(newLayer.getTree().getParentObject()).getCopy();
			if (feature.getTree().getChildren().size() > 1) {
				IGraphicalFeature lastChild = feature.getTree().getChildren().get(feature.getTree().getChildren().indexOf(newLayer.getTree()) - 1).getObject();
				initPos.x = FeatureUIHelper.getLocation(lastChild).x + FeatureUIHelper.getSize(lastChild).width + FMPropertyManager.getFeatureSpaceX();
				initPos.y = FeatureUIHelper.getLocation(lastChild).y;
			} else {
				initPos.y += FMPropertyManager.getFeatureSpaceY();
			}
			FeatureUIHelper.setLocation(newLayer, initPos);
		} else {
			Point initPos = FeatureUIHelper.getLocation(newLayer.getTree().getParentObject()).getCopy();
			if (feature.getTree().getChildren().size() > 1) {
				IGraphicalFeature lastChild = feature.getTree().getChildren().get(feature.getTree().getChildren().indexOf(newLayer.getTree()) - 1).getObject();
				initPos.y = FeatureUIHelper.getLocation(lastChild).y + FeatureUIHelper.getSize(lastChild).height + FMPropertyManager.getFeatureSpaceX();
				initPos.x = FeatureUIHelper.getLocation(lastChild).x;
			} else {
				initPos.x += FeatureUIHelper.getSize(newLayer.getTree().getParentObject()).width + FMPropertyManager.getFeatureSpaceY();
			}
			FeatureUIHelper.setLocation(newLayer, initPos);
		}
	}

	/**
	 * returns the layout manager for the chosen algorithm(id)
	 * 
	 */
	public static FeatureDiagramLayoutManager getLayoutManager(int layoutAlgorithm, IGraphicalFeatureModel featureModel) {
		switch (layoutAlgorithm) {
		case 0:
			return new ManualLayout();
		case 1:
			FeatureUIHelper.setVerticalLayoutBounds(false, featureModel);
			featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
			return new LevelOrderLayout();
		case 2:
			FeatureUIHelper.setVerticalLayoutBounds(false, featureModel);
			featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
			return new BreadthFirstLayout();
		case 3:
			FeatureUIHelper.setVerticalLayoutBounds(false, featureModel);
			featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
			return new DepthFirstLayout();
		case 4:
			FeatureUIHelper.setVerticalLayoutBounds(true, featureModel);
			featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
			return new VerticalLayout();
//		case 5:
//			FeatureUIHelper.setVerticalLayoutBounds(true, featureModel);
//			featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
//			return new VerticalLayout2();
		default:
			FeatureUIHelper.setVerticalLayoutBounds(false, featureModel);
			featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
			return new LevelOrderLayout();
		}

	}
}
