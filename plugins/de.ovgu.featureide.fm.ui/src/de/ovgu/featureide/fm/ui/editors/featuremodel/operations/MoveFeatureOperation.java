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

import static de.ovgu.featureide.fm.core.localization.StringTable.MOVE_FEATURE;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation with functionality to move features. Provides redo/undo support.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 * @author Johannes Herschel
 */
public class MoveFeatureOperation extends AbstractGraphicalFeatureModelOperation {

	private final FeatureOperationData data;
	private final Point newPos;
	private final Point oldPos;
	private boolean or = false;
	private boolean alternative = false;

	public MoveFeatureOperation(IGraphicalFeatureModel graphicalFeatureModel, FeatureOperationData data, Point newPos, Point oldPos) {
		super(graphicalFeatureModel, MOVE_FEATURE);
		this.data = data;
		this.newPos = newPos;
		this.oldPos = oldPos;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(data.getFeatureName());
		final IGraphicalFeature featureGraphical = graphicalFeatureModel.getGraphicalFeature(feature);
		if (!graphicalFeatureModel.getLayout().hasFeaturesAutoLayout()) {
			featureGraphical.setLocation(newPos);
		} else {
			final IFeature oldParent = featureModel.getFeature(data.getOldParentName());
			final IGraphicalFeature oldParentGraphical = graphicalFeatureModel.getGraphicalFeature(oldParent);
			final IFeatureStructure featureStructure = feature.getStructure();

			or = oldParent.getStructure().isOr();
			alternative = oldParent.getStructure().isAlternative();
			oldParent.getStructure().removeChild(featureStructure);

			final IFeature newParent = featureModel.getFeature(data.getNewParentName());
			final IGraphicalFeature newParentGraphical = graphicalFeatureModel.getGraphicalFeature(newParent);

			newParent.getStructure().addChildAtPosition(data.getNewIndex(), featureStructure);
			if (newParentGraphical.isCollapsed()) {
				for (final IFeatureStructure fs : newParent.getStructure().getChildren()) {
					if (fs != featureStructure) {
						final IGraphicalFeature graphicalFS = graphicalFeatureModel.getGraphicalFeature(fs.getFeature());
						graphicalFS.setCollapsed(true);
					}
				}
			}

			if (oldParent != newParent) {
				oldParentGraphical.update(FeatureIDEEvent.getDefault(EventType.CHILDREN_CHANGED));
				newParentGraphical.update(FeatureIDEEvent.getDefault(EventType.CHILDREN_CHANGED));
			}

			if (newParentGraphical.isCollapsed()) {
				newParentGraphical.setCollapsed(false);
				featureModel.fireEvent(new FeatureIDEEvent(newParent, EventType.FEATURE_COLLAPSED_CHANGED, null, null));
			}

			// If there is only one child left, set the old parent group type to and
			if (oldParent.getStructure().getChildrenCount() == 1) {
				oldParent.getStructure().changeToAnd();
			}
		}
		return new FeatureIDEEvent(featureGraphical, EventType.STRUCTURE_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(data.getFeatureName());
		final IGraphicalFeature featureGraphical = graphicalFeatureModel.getGraphicalFeature(feature);
		if (!graphicalFeatureModel.getLayout().hasFeaturesAutoLayout()) {
			featureGraphical.setLocation(oldPos);
		} else {
			final IFeature oldParent = featureModel.getFeature(data.getOldParentName());
			final IFeature newParent = featureModel.getFeature(data.getNewParentName());
			final IFeatureStructure structure2 = feature.getStructure();

			newParent.getStructure().removeChild(structure2);
			oldParent.getStructure().addChildAtPosition(data.getOldIndex(), structure2);

			// When deleting a child and leaving one child behind the group type will be changed to and. reverse to old group type
			if (or) {
				oldParent.getStructure().changeToOr();
			} else if (alternative) {
				oldParent.getStructure().changeToAlternative();
			}
		}
		return new FeatureIDEEvent(featureGraphical, EventType.STRUCTURE_CHANGED);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
