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

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_SIBLING;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFAULT_FEATURE_LAYER_CAPTION;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation with functionality to create a sibling feature. Enables undo/redo functionality.
 *
 * @author Sabrina Hugo
 * @author Christian Orsinger
 */
public class CreateSiblingOperation extends AbstractFeatureModelOperation {

	private final IGraphicalFeatureModel featureModel;
	private final LinkedList<IFeature> selectedFeatures;
	private IFeature newCompound;
	private final int xDistanceTopDown = 5;
	private final int yDistanceLeftRight = 8;
	final IFeatureStructure parent;

	public CreateSiblingOperation(IGraphicalFeatureModel featureModel, LinkedList<IFeature> selectedFeatures) {
		super(featureModel.getFeatureModel(), CREATE_SIBLING);
		this.selectedFeatures = selectedFeatures;
		this.featureModel = featureModel;
		int number = 0;
		while (FeatureUtils.getFeatureNames(featureModel.getFeatureModel()).contains(DEFAULT_FEATURE_LAYER_CAPTION + ++number)) {}

		newCompound =
			FMFactoryManager.getFactory(featureModel.getFeatureModel()).createFeature(featureModel.getFeatureModel(), DEFAULT_FEATURE_LAYER_CAPTION + number);
		parent = selectedFeatures.get(0).getStructure().getParent();
	}

	// finds the parent of the selected features and adds a new child of the parent
	@Override
	protected FeatureIDEEvent operation() {

		parent.addChild(newCompound.getStructure());
		featureModel.getFeatureModel().addFeature(newCompound);
		// checks if manual layout is chosen
		if (featureModel.getLayout().getLayoutAlgorithm() == 0) {
			setPositionNewSibling();
		}

		return new FeatureIDEEvent(featureModel, EventType.FEATURE_ADD_SIBLING, parent != null ? parent.getFeature() : null, newCompound);
	}

	/**
	 * looks for the rightest and lowermost location and places the new feature there, depending on the previous layout
	 */
	private void setPositionNewSibling() {
		final IGraphicalFeature parent = featureModel.getGraphicalFeature(newCompound.getStructure().getParent().getFeature());
		final List<IGraphicalFeature> children = parent.getGraphicalChildren(true);
		int maxX = children.get(0).getLocation().x + children.get(0).getSize().width;
		int yLocation = children.get(0).getLocation().y;
		int maxY = children.get(0).getLocation().y + children.get(0).getSize().height;
		int xLocation = children.get(0).getLocation().x;
		for (int i = 0; i < children.size(); i++) {
			final int rightFeatureBorder = (children.get(i).getLocation().x + children.get(i).getSize().width);
			final int downFeatureBorder = (children.get(i).getLocation().y + children.get(i).getSize().height);
			if (rightFeatureBorder > maxX) {
				maxX = rightFeatureBorder;
				yLocation = children.get(i).getLocation().y;
			}
			if (downFeatureBorder > maxY) {
				maxY = downFeatureBorder;
				xLocation = children.get(i).getLocation().x;
			}
		}

		if (featureModel.getLayout().verticalLayout()) {
			// left to right
			featureModel.getGraphicalFeature(newCompound).setLocation(new Point(xLocation, maxY + yDistanceLeftRight));
		} else {
			featureModel.getGraphicalFeature(newCompound).setLocation(new Point(maxX + xDistanceTopDown, yLocation));
		}
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		newCompound = featureModel.getFeatureModel().getFeature(newCompound.getName());
		featureModel.getFeatureModel().deleteFeature(newCompound);
		return new FeatureIDEEvent(newCompound, EventType.FEATURE_DELETE, null, newCompound);
	}
}
