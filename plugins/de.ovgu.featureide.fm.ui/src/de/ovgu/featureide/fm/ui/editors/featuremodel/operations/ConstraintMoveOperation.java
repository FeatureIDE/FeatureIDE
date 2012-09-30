/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;

/**
 * Operation with functionality to move Constraints. Provides undo/redo
 * functionality.
 * 
 * @author Fabian Benduhn
 */
public class ConstraintMoveOperation extends AbstractFeatureModelOperation {

	private static final String LABEL = "Move Constraint";

	private Constraint constraint;
	private int index;

	private int oldIndex;
	
	private Point newPos;
	private Point oldPos;
	
	public ConstraintMoveOperation(Constraint constraint,
			FeatureModel featureModel, int newIndex, int oldIndex,
			boolean isLastPos, Point newPos, Point oldPos) {

		super(featureModel, LABEL);
		this.constraint = constraint;
		this.index = newIndex;
		this.oldIndex = oldIndex;
		this.newPos = newPos;
		this.oldPos = oldPos;
	}

	@Override
	protected void redo() {
		featureModel.removePropositionalNode(constraint);
		featureModel.addConstraint(constraint, index);
		FeatureUIHelper.setLocation(featureModel.getConstraints().get(index), newPos);
	}
	
	@Override
	protected void undo() {
		featureModel.removePropositionalNode(constraint);
		featureModel.addConstraint(constraint, oldIndex);
		FeatureUIHelper.setLocation(featureModel.getConstraints().get(index), oldPos);
	}

}
