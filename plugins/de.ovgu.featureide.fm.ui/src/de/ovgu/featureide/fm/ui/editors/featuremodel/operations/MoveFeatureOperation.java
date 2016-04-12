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

import static de.ovgu.featureide.fm.core.localization.StringTable.MOVE_FEATURE;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;

/**
 * Operation with functionality to move features. Provides redo/undo support.
 * 
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class MoveFeatureOperation extends AbstractFeatureModelOperation {

	private FeatureOperationData data;
	private Point newPos;
	private Point oldPos;

	public MoveFeatureOperation(FeatureOperationData data, Object editor, Point newPos, Point oldPos, IFeature feature) {
		super(feature.getFeatureModel(), MOVE_FEATURE);
		this.data = data;
		this.newPos = newPos;
		this.oldPos = oldPos;
		setEditor(editor);
		setEventId(FeatureIDEEvent.STRUCTURE_CHANGED);
	}

	public void newInnerOrder(Point newPos) {
		FeatureUIHelper.setLocation(data.getFeature(), newPos);
	}

	@Override
	protected FeatureIDEEvent operation() {
		if (!data.getFeature().getGraphicalModel().getLayout().hasFeaturesAutoLayout()) {
			newInnerOrder(newPos);
			setEventId(FeatureIDEEvent.MODEL_DATA_LOADED);
		} else {
			data.getOldParent().getObject().getStructure().removeChild(data.getFeature().getObject().getStructure());
			data.getNewParent().getObject().getStructure().addChildAtPosition(data.getNewIndex(), data.getFeature().getObject().getStructure());
		}
		return null;
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		if (!data.getFeature().getGraphicalModel().getLayout().hasFeaturesAutoLayout()) {
			newInnerOrder(oldPos);
			setEventId(FeatureIDEEvent.MODEL_DATA_LOADED);
		} else {
			final IFeatureStructure structure2 = data.getFeature().getObject().getStructure();
			data.getNewParent().getObject().getStructure().removeChild(structure2);
			if (data.getOldParent() != null) {
				final IFeatureStructure structure = data.getOldParent().getObject().getStructure();
				structure.addChildAtPosition(data.getOldIndex(), structure2);
			}
		}
		return null;
	}

}
