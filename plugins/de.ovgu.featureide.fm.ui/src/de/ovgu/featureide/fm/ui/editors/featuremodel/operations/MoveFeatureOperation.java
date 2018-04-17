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

import static de.ovgu.featureide.fm.core.localization.StringTable.MOVE_FEATURE;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;

/**
 * Operation with functionality to move features. Provides redo/undo support.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class MoveFeatureOperation extends AbstractFeatureModelOperation {

	private final FeatureOperationData data;
	private final Point newPos;
	private final Point oldPos;
	private boolean or = false;
	private boolean alternative = false;

	public MoveFeatureOperation(FeatureOperationData data, Object editor, Point newPos, Point oldPos, IFeature feature) {
		super(feature.getFeatureModel(), MOVE_FEATURE);
		this.data = data;
		this.newPos = newPos;
		this.oldPos = oldPos;
		setEditor(editor);
	}

	public void newInnerOrder(Point newPos) {
		data.getFeature().setLocation(newPos);
	}

	@Override
	protected FeatureIDEEvent operation() {
		final IGraphicalFeature feature = data.getFeature();
		final IGraphicalFeature oldParent = data.getOldParent();
		if (!feature.getGraphicalModel().getLayout().hasFeaturesAutoLayout()) {
			newInnerOrder(newPos);
		} else {
			final IFeatureStructure featureStructure = feature.getObject().getStructure();

			or = oldParent.getObject().getStructure().isOr();
			alternative = oldParent.getObject().getStructure().isAlternative();
			oldParent.getObject().getStructure().removeChild(featureStructure);

			final IGraphicalFeature newParent = data.getNewParent();

			if (newParent.isCollapsed()) {
				newParent.getObject().getStructure().addChildAtPosition(newParent.getObject().getStructure().getChildrenCount() + 1, featureStructure);

				for (final IFeatureStructure fs : newParent.getObject().getStructure().getChildren()) {
					if (fs != featureStructure) {
						final IGraphicalFeature graphicalFS = feature.getGraphicalModel().getGraphicalFeature(fs.getFeature());
						graphicalFS.setCollapsed(true);
					}
				}
			} else {
				newParent.getObject().getStructure().addChildAtPosition(data.getNewIndex(), featureStructure);
			}

			if (oldParent != newParent) {
				oldParent.update(FeatureIDEEvent.getDefault(EventType.CHILDREN_CHANGED));
				newParent.update(FeatureIDEEvent.getDefault(EventType.CHILDREN_CHANGED));
			}

			if (newParent.isCollapsed()) {
				newParent.setCollapsed(false);
				feature.getGraphicalModel().getFeatureModel().fireEvent(new FeatureIDEEvent(newParent.getObject(), EventType.COLLAPSED_CHANGED, null, null));
			}
		}
		// If there is only one child left, set the old parent group type to and
		if (oldParent != null) {
			if (oldParent.getObject().getStructure().getChildrenCount() == 1) {
				oldParent.getObject().getStructure().changeToAnd();
			}
		}
		return new FeatureIDEEvent(feature, EventType.STRUCTURE_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		if (!data.getFeature().getGraphicalModel().getLayout().hasFeaturesAutoLayout()) {
			newInnerOrder(oldPos);
		} else {
			final IFeatureStructure structure2 = data.getFeature().getObject().getStructure();
			data.getNewParent().getObject().getStructure().removeChild(structure2);
			if (data.getOldParent() != null) {
				final IFeatureStructure structure = data.getOldParent().getObject().getStructure();
				structure.addChildAtPosition(data.getOldIndex(), structure2);
			}

		}
		// When deleting a child and leaving one child behind the group type will be changed to and. reverse to old group type
		if ((data.getOldParent() != null) && or) {
			data.getOldParent().getObject().getStructure().changeToOr();
		} else if ((data.getOldParent() != null) && alternative) {
			data.getOldParent().getObject().getStructure().changeToAlternative();
		}
		return new FeatureIDEEvent(data.getFeature(), EventType.STRUCTURE_CHANGED);
	}

}
