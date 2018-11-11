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

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_FEATURE_ABOVE;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFAULT_FEATURE_LAYER_CAPTION;

import java.util.Collections;
import java.util.TreeMap;
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
 * Operation with functionality to create a compound feature. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class CreateFeatureAboveOperation extends AbstractFeatureModelOperation {

	private final IFeature newCompound;
	private final IFeature child;
	private final IGraphicalFeature newGraphicalFeature;
	private int distance;
	LinkedList<IFeature> selectedFeatures;
	TreeMap<Integer, IFeature> children = new TreeMap<>();

	boolean parentOr = false;
	boolean parentAlternative = false;

	private final int topDownDefaultDistance = 50;
	private final int leftRightDefaultDistance = 120;

	public CreateFeatureAboveOperation(IGraphicalFeatureModel featureModel, LinkedList<IFeature> selectedFeatures) {
		super(featureModel.getFeatureModel(), CREATE_FEATURE_ABOVE);
		this.selectedFeatures = selectedFeatures;
		child = selectedFeatures.get(0);
		int number = 0;
		while (FeatureUtils.getFeatureNames(featureModel.getFeatureModel()).contains(DEFAULT_FEATURE_LAYER_CAPTION + ++number)) {}

		newCompound =
			FMFactoryManager.getFactory(featureModel.getFeatureModel()).createFeature(featureModel.getFeatureModel(), DEFAULT_FEATURE_LAYER_CAPTION + number);

		newGraphicalFeature = featureModel.getGraphicalFeature(newCompound);
	}

	@Override
	protected FeatureIDEEvent operation() {
		final IFeatureStructure parent = child.getStructure().getParent();
		if (parent != null) {
			parentOr = parent.isOr();
			parentAlternative = parent.isAlternative();

			newCompound.getStructure().setMultiple(parent.isMultiple());
			final int index = parent.getChildIndex(child.getStructure());
			for (final IFeature iFeature : selectedFeatures) {
				children.put(parent.getChildIndex(iFeature.getStructure()), iFeature);
			}
			for (final IFeature iFeature : selectedFeatures) {
				parent.removeChild(iFeature.getStructure());
			}
			parent.addChildAtPosition(index, newCompound.getStructure());
			for (final IFeature iFeature : selectedFeatures) {
				newCompound.getStructure().addChild(iFeature.getStructure());
			}

			if (parentOr) {
				newCompound.getStructure().changeToOr();
			} else if (parentAlternative) {
				newCompound.getStructure().changeToAlternative();
			} else {
				newCompound.getStructure().changeToAnd();
			}
			parent.changeToAnd();
			featureModel.addFeature(newCompound);
		} else {
			newCompound.getStructure().addChild(child.getStructure());
			featureModel.addFeature(newCompound);
			featureModel.getStructure().setRoot(newCompound.getStructure());
		}

		if (newGraphicalFeature.getGraphicalModel().getLayout().getLayoutAlgorithm() == 0) {
			adjustPositions();
		}

		return new FeatureIDEEvent(featureModel, EventType.FEATURE_ADD_ABOVE, parent != null ? parent.getFeature() : null, newCompound);
	}

	/**
	 * adjusts position of the new feature and its children in manual layout
	 */
	private void adjustPositions() {
		final List<IGraphicalFeature> graphicalChildren = newGraphicalFeature.getGraphicalChildren(true);
		int minX = graphicalChildren.get(0).getLocation().x;
		int minY = graphicalChildren.get(0).getLocation().y;
		int yLocation = graphicalChildren.get(0).getLocation().y;
		int xLocation = graphicalChildren.get(0).getLocation().x;

		// looks for the leftest x coordinate and the topmost y coordinate of a child
		for (final IGraphicalFeature child : graphicalChildren) {
			if (child.getLocation().x < minX) {
				minX = child.getLocation().x;
				yLocation = child.getLocation().y;
			}
			if (child.getLocation().y < minY) {
				minY = child.getLocation().y;
				xLocation = child.getLocation().x;
			}
		}

		// decides if the anchor points are at the side or on the top of the rectangle
		int distance;
		boolean topDown;
		if (!newGraphicalFeature.getGraphicalModel().getLayout().getHasVerticalLayout()) {
			newGraphicalFeature.setLocation(new Point(minX, yLocation));
			topDown = true;
			distance = topDownDefaultDistance;
		} else {
			newGraphicalFeature.setLocation(new Point(xLocation, minY));
			topDown = false;
			distance = leftRightDefaultDistance;
		}
		this.distance = distance;
		shiftChildren(graphicalChildren, distance, topDown);
	}

	/**
	 * shifts the subtree of the new feature above
	 *
	 * @param graphicalChildren children of the new feature
	 * @param distance distance to shift
	 * @param topDown previous layout
	 */
	private void shiftChildren(List<IGraphicalFeature> graphicalChildren, int distance, boolean topDown) {
		for (int i = 0; i < graphicalChildren.size(); i++) {
			shiftChildren(graphicalChildren.get(i).getGraphicalChildren(true), distance, topDown);
			// if there are more layouts to come, there has to be more cases added here
			if (topDown) {
				graphicalChildren.get(i).setLocation(new Point(graphicalChildren.get(i).getLocation().x, graphicalChildren.get(i).getLocation().y + distance));
			} else {
				graphicalChildren.get(i).setLocation(new Point(graphicalChildren.get(i).getLocation().x + distance, graphicalChildren.get(i).getLocation().y));
			}
		}
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		final IFeatureStructure parent = newCompound.getStructure().getParent();
		if (newGraphicalFeature.getGraphicalModel().getLayout().getLayoutAlgorithm() == 0) {
			shiftChildren(newGraphicalFeature.getGraphicalChildren(true), (-distance), !newGraphicalFeature.getGraphicalModel().getLayout().getHasVerticalLayout());
		}
		if (parent != null) {
			newCompound.getStructure().setChildren(Collections.<IFeatureStructure> emptyList());
			featureModel.deleteFeature(newCompound);
			for (final Integer position : children.keySet()) {
				parent.addChildAtPosition(position, children.get(position).getStructure());
			}

			if (parentOr) {
				parent.changeToOr();
			} else if (parentAlternative) {
				parent.changeToAlternative();
			} else {
				parent.changeToAnd();
			}
		} else {
			featureModel.getStructure().replaceRoot(child.getStructure());
			newCompound.getStructure().removeChild(child.getStructure());
			return new FeatureIDEEvent(newCompound, EventType.FEATURE_DELETE, null, null);
		}
		return new FeatureIDEEvent(newCompound, EventType.FEATURE_DELETE, parent.getFeature(), null);
	}

}
