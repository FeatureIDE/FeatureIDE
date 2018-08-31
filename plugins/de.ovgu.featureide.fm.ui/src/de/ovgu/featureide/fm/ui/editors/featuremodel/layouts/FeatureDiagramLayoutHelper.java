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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import static de.ovgu.featureide.fm.core.localization.StringTable.LONG_NAMES;
import static de.ovgu.featureide.fm.core.localization.StringTable.MANUAL_LAYOUT;
import static de.ovgu.featureide.fm.core.localization.StringTable.SHORT_NAMES;

import java.util.LinkedList;
import java.util.List;

import org.abego.treelayout.Configuration;
import org.abego.treelayout.Configuration.Location;
import org.abego.treelayout.util.DefaultConfiguration;
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
 * @author Marcus Pinnecke
 * @author Lukas Vogt
 * @author Martha Nyerembe
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
			return "Root Top (abego TreeLayout)";
		case 6:
			return "Root Left (abego TreeLayout)";
		case 7:
			return "Root Right (abego TreeLayout)";
		case 8:
			return "Root Bottom (abego TreeLayout)";
		default:
			return "Top-Down (ordered)";
		}
	}

	/**
	 * returns label texts (e.g. for the context menu)
	 */
	public static String getNameTypeLabel(int layoutType) {
		switch (layoutType) {
		case 1:
			return SHORT_NAMES;
		case 0:
		default:
			return LONG_NAMES;
		}
	}

	/**
	 * sets initial positions for new constraints needed for manual layout
	 */
	public static void initializeConstraintPosition(IGraphicalFeatureModel featureModel, int index) {
		Point newLocation = new Point(0, 0);
		final IGraphicalConstraint constraint = featureModel.getVisibleConstraints().get(index);
		int leftX = Integer.MAX_VALUE;
		int rightX = Integer.MIN_VALUE;
		final int constraintCount = featureModel.getVisibleConstraints().size();
		if (constraintCount == 1) {
			for (final IGraphicalFeature feature : featureModel.getVisibleFeatures()) {
				if (feature.getLocation().y > newLocation.y) {
					newLocation.y = feature.getLocation().y;
				}
				if (feature.getLocation().x > rightX) {
					rightX = feature.getLocation().x;
				}
				if (feature.getLocation().x < leftX) {
					leftX = feature.getLocation().x;
				}
			}
			newLocation.x = (leftX + rightX) / 2;
			newLocation.y += FMPropertyManager.getFeatureSpaceY();
		} else {
			final IGraphicalConstraint lastConstraint = featureModel.getVisibleConstraints().get(constraintCount - 2);
			newLocation = lastConstraint.getLocation().getCopy();
			newLocation.y += FMPropertyManager.getConstraintSpace();
		}
		constraint.setLocation(newLocation);
	}

	/**
	 * sets initial positions for new features (above) needed for manual layout
	 */
	public static void initializeCompoundFeaturePosition(IGraphicalFeatureModel featureModel, LinkedList<IGraphicalFeature> selectedFeatures,
			IGraphicalFeature newCompound) {
		final Point initPos = new Point(0, 0);
		int xAcc = 0;
		for (final IGraphicalFeature feature : selectedFeatures) {
			if (initPos.y < feature.getLocation().y) {
				initPos.y = feature.getLocation().y;
			}
			xAcc += feature.getLocation().x;
		}
		initPos.x = (xAcc / selectedFeatures.size());
		if (newCompound.getObject().getStructure().isRoot()) {
			initPos.y = (initPos.y - FMPropertyManager.getFeatureSpaceY());
		} else {
			final IGraphicalFeature parent = FeatureUIHelper.getGraphicalParent(newCompound);
			initPos.y = (initPos.y + parent.getLocation().y) / 2;
			initPos.x = (initPos.x + parent.getLocation().x) / 2;
		}
		newCompound.setLocation(initPos);

	}

	/**
	 * sets initial positions for new features (below) needed for manual layout
	 */
	public static void initializeLayerFeaturePosition(IGraphicalFeatureModel featureModel, IGraphicalFeature newLayer, IGraphicalFeature feature) {
		final List<IGraphicalFeature> graphicalChildren = FeatureUIHelper.getGraphicalChildren(feature);
		if (!FeatureUIHelper.hasVerticalLayout(featureModel)) {
			final Point initPos = FeatureUIHelper.getGraphicalParent(newLayer).getLocation().getCopy();
			if (feature.getObject().getStructure().getChildrenCount() > 1) {
				final IGraphicalFeature lastChild = graphicalChildren.get(graphicalChildren.indexOf(newLayer) - 1);
				initPos.x = lastChild.getLocation().x + lastChild.getSize().width + FMPropertyManager.getFeatureSpaceX();
				initPos.y = lastChild.getLocation().y;
			} else {
				initPos.y += FMPropertyManager.getFeatureSpaceY();
			}
			newLayer.setLocation(initPos);
		} else {
			final Point initPos = FeatureUIHelper.getGraphicalParent(newLayer).getLocation().getCopy();
			if (graphicalChildren.size() > 1) {
				final IGraphicalFeature lastChild = graphicalChildren.get(graphicalChildren.indexOf(newLayer) - 1);
				initPos.y = lastChild.getLocation().y + lastChild.getSize().height + FMPropertyManager.getFeatureSpaceX();
				initPos.x = lastChild.getLocation().x;
			} else {
				initPos.x += FeatureUIHelper.getGraphicalParent(newLayer).getSize().width + FMPropertyManager.getFeatureSpaceY();
			}
			newLayer.setLocation(initPos);
		}
	}

	/**
	 * returns the layout manager for the chosen algorithm(id)
	 *
	 */
	public static FeatureDiagramLayoutManager getLayoutManager(int layoutAlgorithm, IGraphicalFeatureModel featureModel) {
		switch (layoutAlgorithm) {
		case 0:
//			FeatureUIHelper.setVerticalLayoutBounds(false, featureModel);
//			featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
			return new ManualLayout();
		case 1:
			featureModel.getLayout().setUsesAbegoTreeLayout(false);
			FeatureUIHelper.setVerticalLayoutBounds(false, featureModel);
			featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
			return new LevelOrderLayout();
		case 2:
			featureModel.getLayout().setUsesAbegoTreeLayout(false);
			FeatureUIHelper.setVerticalLayoutBounds(false, featureModel);
			featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
			return new BreadthFirstLayout();
		case 3:
			featureModel.getLayout().setUsesAbegoTreeLayout(false);
			FeatureUIHelper.setVerticalLayoutBounds(false, featureModel);
			featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
			return new DepthFirstLayout();
		case 4:
			featureModel.getLayout().setUsesAbegoTreeLayout(false);
			FeatureUIHelper.setVerticalLayoutBounds(true, featureModel);
			featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
			return new VerticalLayout();
//			the following cases are for Tree Layout using abego Tree Layout library
		case 5:
			final Location top = Configuration.Location.Top;
			featureModel.getLayout().setAbegoRootposition(top);
			return new FTreeLayout(new DefaultConfiguration<IGraphicalFeature>(30.0, 5.0, top, Configuration.AlignmentInLevel.TowardsRoot));
		case 6:
			final Location left = Configuration.Location.Left;
			featureModel.getLayout().setAbegoRootposition(left);
			return new FTreeLayout(new DefaultConfiguration<IGraphicalFeature>(40, 10, left, Configuration.AlignmentInLevel.TowardsRoot));
		case 7:
			final Location right = Configuration.Location.Right;
			featureModel.getLayout().setAbegoRootposition(right);
			return new FTreeLayout(new DefaultConfiguration<IGraphicalFeature>(30, 15, right, Configuration.AlignmentInLevel.TowardsRoot));
		case 8:
			final Location bottom = Configuration.Location.Bottom;
			featureModel.getLayout().setAbegoRootposition(bottom);
			return new FTreeLayout(new DefaultConfiguration<IGraphicalFeature>(30, 5, bottom, Configuration.AlignmentInLevel.AwayFromRoot));
		default:
			FeatureUIHelper.setVerticalLayoutBounds(false, featureModel);
			featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
			return new LevelOrderLayout();
		}

	}
}
