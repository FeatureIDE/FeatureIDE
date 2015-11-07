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

import static de.ovgu.featureide.fm.core.localization.StringTable.MOVE_CONSTRAINT;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;

/**
 * Operation with functionality to move Constraints. Provides undo/redo
 * functionality.
 * 
 * @author Fabian Benduhn
 */
public class ConstraintMoveOperation extends AbstractFeatureModelOperation {

	private static final String LABEL = MOVE_CONSTRAINT;

	private IConstraint constraint;
	private int index;

	private int oldIndex;

	private Point newPos;
	private Point oldPos;

	public ConstraintMoveOperation(IConstraint constraint, IFeatureModel featureModel, int newIndex, int oldIndex, boolean isLastPos, Point newPos, Point oldPos) {

		super(featureModel, LABEL);
		this.constraint = constraint;
		this.index = newIndex;
		this.oldIndex = oldIndex;
		this.newPos = newPos;
		this.oldPos = oldPos;
	}

	@Override
	protected void redo() {
		featureModel.removeConstraint(constraint);
		featureModel.addConstraint(constraint, index);
		FeatureUIHelper.setLocation(featureModel.getConstraints().get(index).getGraphicRepresenation(), newPos);
	}

	@Override
	protected void undo() {
		featureModel.removeConstraint(constraint);
		featureModel.addConstraint(constraint, oldIndex);
		FeatureUIHelper.setLocation(featureModel.getConstraints().get(index).getGraphicRepresenation(), oldPos);
	}

}
