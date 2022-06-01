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

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_CONSTRAINT;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation to delete a constraint.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class DeleteConstraintOperation extends AbstractFeatureModelOperation {

	public static final String ID = ID_PREFIX + "DeleteConstraintOperation";

	private final IConstraint constraint;
	private int oldConstraintIndex;

	public DeleteConstraintOperation(IConstraint constraint, IFeatureModelManager featureModelManager) {
		super(featureModelManager, DELETE_CONSTRAINT);
		this.constraint = constraint;
	}

	@Override
	protected FeatureIDEEvent firstOperation(IFeatureModel featureModel) {
		oldConstraintIndex = featureModel.getConstraintIndex(constraint);
		return operation(featureModel);
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		if (oldConstraintIndex != -1) {
			// The deleted constraint, may be different from oldConstraint if this is a redo operation
			final IConstraint deletedConstraint = featureModel.getConstraints().get(oldConstraintIndex);
			featureModel.removeConstraint(oldConstraintIndex);
			return new FeatureModelOperationEvent(ID, EventType.CONSTRAINT_DELETE, featureModel, deletedConstraint, null);
		}
		return new FeatureModelOperationEvent(ID, EventType.CONSTRAINT_DELETE, featureModel, null, null);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		if (oldConstraintIndex != -1) {
			final IConstraint constraint = FMFactoryManager.getInstance().getFactory(featureModel).copyConstraint(featureModel, this.constraint);
			featureModel.addConstraint(constraint, oldConstraintIndex);
			return new FeatureModelOperationEvent(ID, EventType.CONSTRAINT_ADD, featureModel, null, constraint);
		}
		return new FeatureModelOperationEvent(ID, EventType.CONSTRAINT_ADD, featureModel, null, null);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
