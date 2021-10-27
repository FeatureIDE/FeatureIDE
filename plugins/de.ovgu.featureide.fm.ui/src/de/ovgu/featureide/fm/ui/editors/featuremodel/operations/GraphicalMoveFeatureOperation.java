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
 * Operation with functionality to move features graphically. Provides redo/undo support.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 * @author Benedikt Jutz
 */
public class GraphicalMoveFeatureOperation extends AbstractGraphicalFeatureModelOperation {

	private final FeatureOperationData data;
	private final Point newPos;
	private final Point oldPos;

	public GraphicalMoveFeatureOperation(IGraphicalFeatureModel graphicalFeatureModel, FeatureOperationData data, Point newPos, Point oldPos) {
		super(graphicalFeatureModel, MOVE_FEATURE);
		this.data = data;
		this.newPos = newPos;
		this.oldPos = oldPos;
	}

	public void newInnerOrder(Point newPos) {
		data.feature.setLocation(newPos);
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IGraphicalFeature feature = data.feature;
		final IGraphicalFeature oldParent = data.oldParent;
		final IFeature oldParentObject = oldParent.getObject();
		final IFeatureStructure oldParentStructure = oldParentObject.getStructure();

		final boolean usingAutoLayout = graphicalFeatureModel.getLayout().hasFeaturesAutoLayout();
		if (!usingAutoLayout) {
			newInnerOrder(newPos);
		} else {
			final IFeature featureObject = feature.getObject();
			final IFeatureStructure featureStructure = featureObject.getStructure();
			oldParentStructure.removeChild(featureStructure);

			final IGraphicalFeature newParent = data.newParent;

			final IFeatureStructure newParentStructure = newParent.getObject().getStructure();
			if (newParent.isCollapsed()) {
				newParentStructure.addChildAtPosition(newParentStructure.getChildrenCount() + 1, featureStructure);

				for (final IFeatureStructure fs : newParentStructure.getChildren()) {
					if (fs != featureStructure) {
						final IGraphicalFeature graphicalFS = graphicalFeatureModel.getGraphicalFeature(fs.getFeature());
						graphicalFS.setCollapsed(true);
					}
				}
			} else {
				newParentStructure.addChildAtPosition(data.newIndex, featureStructure);
			}

			if (oldParent != newParent) {
				oldParent.update(FeatureIDEEvent.getDefault(EventType.CHILDREN_CHANGED));
				newParent.update(FeatureIDEEvent.getDefault(EventType.CHILDREN_CHANGED));
			}

			if (newParent.isCollapsed()) {
				newParent.setCollapsed(false);
				featureModel.fireEvent(new FeatureIDEEvent(newParent.getObject(), EventType.FEATURE_COLLAPSED_CHANGED, null, null));
			}

			if (data.reverse) {
				if (data.or) {
					newParentStructure.setOr();
				}
				if (data.alternative) {
					newParentStructure.setAlternative();
				}
			}
		}
		// If only one child remains, set the old parent's group to and.
		if (oldParent != null) {
			if (oldParentStructure.getChildrenCount() == 1) {
				oldParentStructure.changeToAnd();
			}
		}
		return new FeatureIDEEvent(feature, EventType.STRUCTURE_CHANGED, usingAutoLayout, data);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final boolean useAutoLayout = graphicalFeatureModel.getLayout().hasFeaturesAutoLayout();
		if (!useAutoLayout) {
			newInnerOrder(oldPos);
		} else {
			final IFeatureStructure structure2 = data.feature.getObject().getStructure();
			data.newParent.getObject().getStructure().removeChild(structure2);
			if (data.oldParent != null) {
				final IFeatureStructure structure = data.oldParent.getObject().getStructure();
				structure.addChildAtPosition(data.oldIndex, structure2);
			}

		}
		// When deleting a child and leaving one child behind the group type will be changed to and. reverse to old group type
		if ((data.oldParent != null) && data.or) {
			data.oldParent.getObject().getStructure().changeToOr();
		} else if ((data.oldParent != null) && data.alternative) {
			data.oldParent.getObject().getStructure().changeToAlternative();
		}
		return new FeatureIDEEvent(data.feature, EventType.STRUCTURE_CHANGED, useAutoLayout, data.getInverseData());
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
