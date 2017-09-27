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
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.commands.Command;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.MoveConstraintOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.MoveConstraintToLocationOperation;

/**
 * Executed command when dragging and dropping constraints
 *
 * @author Fabian Benduhn
 * @author David Broneske
 * @author Marcus Pinnecke
 */
public class ConstraintDragAndDropCommand extends Command {

	private int maxLeft;
	private int maxRight;
	private int maxUp;
	private int maxDown;
	private final IGraphicalFeatureModel featureModel;
	private final IGraphicalConstraint constraint;
	private final Point newLocation;
	private final boolean hasAutoLayout;
	boolean isLastPos;

	public ConstraintDragAndDropCommand(IGraphicalFeatureModel featureModel, IGraphicalConstraint constraint, Point newLocation) {
		// super("Moving " + constraint.getNode().toString());
		this.featureModel = featureModel;
		this.constraint = constraint;
		this.newLocation = newLocation;
		isLastPos = false;
		hasAutoLayout = featureModel.getLayout().hasFeaturesAutoLayout();
	}

	@Override
	public boolean canExecute() {
		if (hasAutoLayout) {
			setMaxValues();
			if ((newLocation.y > (maxDown + 30)) || (newLocation.y < (maxUp - 10)) || (newLocation.x > (maxRight + 5)) || (newLocation.x < (maxLeft - 5))) {
				return false;
			}
		}
		return true;
	}

	@Override
	public void execute() {

		int index = calculateNewIndex();
		final int oldIndex = featureModel.getConstraints().indexOf(constraint);
		if ((index > oldIndex) && !isLastPos) {
			index--;
		}
		if (hasAutoLayout && (index == oldIndex)) {
			return;
		}

		AbstractFeatureModelOperation op = null;
		if (hasAutoLayout) {
			op = new MoveConstraintOperation(constraint.getObject(), featureModel.getFeatureModel(), index, oldIndex);
			op.addContext((IUndoContext) featureModel.getFeatureModel().getUndoContext());
		} else {
			op = new MoveConstraintToLocationOperation(featureModel, newLocation, constraint.getObject());
		}
		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}

	}

	/**
	 *
	 */
	private int calculateNewIndex() {
		for (final IGraphicalConstraint c : featureModel.getConstraints()) {
			if ((c.getLocation().y + 17) > newLocation.y) {
				isLastPos = false;

				return featureModel.getConstraints().indexOf(c);

			}

		}
		isLastPos = true;
		return featureModel.getConstraints().size() - 1;
	}

	public void setMaxValues() {
		maxLeft = constraint.getLocation().x;
		maxUp = constraint.getLocation().y;
		for (final IGraphicalConstraint c : featureModel.getConstraints()) {

			if (c.getLocation().x < maxLeft) {
				maxLeft = c.getLocation().x;
			}
			if (c.getLocation().y < maxUp) {
				maxUp = c.getLocation().y;

			}
			if ((c.getLocation().x + c.getSize().width) > maxRight) {
				maxRight = c.getLocation().x + c.getSize().width;
			}
			if ((c.getLocation().y + c.getSize().height) > maxDown) {
				maxDown = c.getLocation().y + c.getSize().height;
			}

		}

	}

	/**
	 *
	 */
	public Point getLeftPoint() {
		final int index = calculateNewIndex();

		final Point p = new Point(constraint.getLocation().x - 5, featureModel.getConstraints().get(index).getLocation().y);
		if (isLastPos) {
			p.y = p.y + 17;

		}
		return p;

	}

	public Point getRightPoint() {

		final Point p =
			new Point(constraint.getLocation().x + constraint.getSize().width + 5, featureModel.getConstraints().get(calculateNewIndex()).getLocation().y);
		if (isLastPos) {
			p.y = p.y + 17;

		}
		return p;
	}
}
