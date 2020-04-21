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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_SIBLING;

import java.util.List;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation with functionality to create a sibling feature. Enables undo/redo functionality.
 *
 * @author Sabrina Hugo
 * @author Christian Orsinger
 */
public class CreateGraphicalSiblingOperation extends AbstractGraphicalFeatureModelOperation {

	private static final int xDistanceTopDown = 5;
	private static final int yDistanceLeftRight = 8;

	private final String selectedFeatureName;

	private CreateFeatureOperation createFeatureOperation;

	public CreateGraphicalSiblingOperation(IGraphicalFeatureModel featureModel, String selectedFeatureName) {
		super(featureModel, CREATE_SIBLING);
		this.selectedFeatureName = selectedFeatureName;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IFeature selectedFeature = featureModel.getFeature(selectedFeatureName);
		final IFeature parent = FeatureUtils.getParent(selectedFeature);
		if (parent != null) {
			final int index = parent.getStructure().getChildIndex(selectedFeature.getStructure()) + 1;
			createFeatureOperation = new CreateFeatureOperation(parent.getName(), index, featureModelManager);
			final FeatureIDEEvent event = createFeatureOperation.operation(featureModel);
			if (event != null) {
				final IFeature newFeature = (IFeature) event.getNewValue();
				// checks if manual layout is chosen
				if (graphicalFeatureModel.getLayout().getLayoutAlgorithm() == 0) {
					final IGraphicalFeature graphicalParent = graphicalFeatureModel.getGraphicalFeature(parent);
					final List<IGraphicalFeature> children = graphicalParent.getGraphicalChildren();
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

					if (graphicalFeatureModel.getLayout().hasVerticalLayout()) {
						// left to right
						graphicalFeatureModel.getGraphicalFeature(newFeature).setLocation(new Point(xLocation, maxY + yDistanceLeftRight));
					} else {
						graphicalFeatureModel.getGraphicalFeature(newFeature).setLocation(new Point(maxX + xDistanceTopDown, yLocation));
					}
				}
				return new FeatureIDEEvent(featureModel, EventType.FEATURE_ADD_SIBLING, parent != null ? parent : null, newFeature);
			}
		}
		return null;
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		return createFeatureOperation != null ? createFeatureOperation.inverseOperation(featureModel) : null;
	}

	@Override
	protected int getChangeIndicator() {
		// The operation creates features internally => change indicator to CHANGE_DEPENDENCIES
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}
}
