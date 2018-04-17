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

import static de.ovgu.featureide.fm.core.localization.StringTable.MOVE_CONSTRAINT;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation to move constraints to the new mouse positione when manual layout is activated
 *
 * @author Joshua Sprey
 */
public class MoveConstraintToLocationOperation extends AbstractFeatureModelOperation {

	private final Point newPos;
	private Point oldPos;
	private final IGraphicalFeatureModel graphicalFeatureModel;
	private final IConstraint constraint;

	public MoveConstraintToLocationOperation(IGraphicalFeatureModel graphicalFeatureModel, Point newPos, IConstraint constraint) {
		super(graphicalFeatureModel.getFeatureModel(), MOVE_CONSTRAINT);
		this.graphicalFeatureModel = graphicalFeatureModel;
		this.constraint = constraint;
		this.newPos = newPos;
	}

	@Override
	protected FeatureIDEEvent operation() {
		oldPos = graphicalFeatureModel.getGraphicalConstraint(constraint).getLocation();
		graphicalFeatureModel.getGraphicalConstraint(constraint).setLocation(newPos);
		return FeatureIDEEvent.getDefault(EventType.CONSTRAINT_MOVE);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		graphicalFeatureModel.getGraphicalConstraint(constraint).setLocation(oldPos);
		return FeatureIDEEvent.getDefault(EventType.CONSTRAINT_MOVE);
	}

}
