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

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_CONSTRAINT;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;

/**
 * Operation to delete a constraint.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class DeleteConstraintOperation extends AbstractFeatureModelOperation {

	private final IConstraint constraint;

	private int index;

	public DeleteConstraintOperation(IConstraint constraint, IFeatureModel featureModel) {
		super(featureModel, DELETE_CONSTRAINT);
		this.constraint = constraint;
	}

	@Override
	protected FeatureIDEEvent operation() {
		index = featureModel.getConstraintIndex(constraint);
		featureModel.removeConstraint(constraint);
		return new FeatureIDEEvent(featureModel, EventType.CONSTRAINT_DELETE, constraint, null);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		featureModel.addConstraint(constraint, index);
		return new FeatureIDEEvent(featureModel, EventType.CONSTRAINT_ADD, null, constraint);
	}

}
