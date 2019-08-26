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

import static de.ovgu.featureide.fm.core.localization.StringTable.MOVE_CONSTRAINT;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation with functionality to move Constraints. Provides undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class MoveConstraintOperation extends AbstractFeatureModelOperation {

	private final int newIndex, oldIndex;

	public MoveConstraintOperation(IFeatureModelManager featureModelManager, int newIndex, int oldIndex) {
		super(featureModelManager, MOVE_CONSTRAINT);
		this.newIndex = newIndex;
		this.oldIndex = oldIndex;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IConstraint constraint = featureModel.getConstraints().get(oldIndex);
		featureModel.removeConstraint(oldIndex);
		featureModel.addConstraint(constraint, newIndex);
		return new FeatureIDEEvent(constraint, EventType.CONSTRAINT_MOVE, oldIndex, newIndex);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IConstraint constraint = featureModel.getConstraints().get(newIndex);
		featureModel.removeConstraint(newIndex);
		featureModel.addConstraint(constraint, oldIndex);
		return new FeatureIDEEvent(constraint, EventType.CONSTRAINT_MOVE, newIndex, oldIndex);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_GRAPHICS;
	}

}
