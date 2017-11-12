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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.AUTO_LAYOUT_CONSTRAINTS;

import java.util.LinkedList;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AutoLayoutConstraintOperation;

/**
 * Action to switch auto-layout for contraints on/off.
 *
 * @author David Halm
 * @author Patrick Sulkowski
 * @author Marcus Pinnecke (Feature Interface)
 */
public class AutoLayoutConstraintAction extends Action {

	public static final String ID = "de.ovgu.featureide.autolayoutconstraint";

	private final IGraphicalFeatureModel featureModel;
	private final LinkedList<LinkedList<Point>> oldPos = new LinkedList<LinkedList<Point>>();

	public AutoLayoutConstraintAction(GraphicalViewerImpl viewer, IGraphicalFeatureModel featureModel) {
		super(AUTO_LAYOUT_CONSTRAINTS);
		this.featureModel = featureModel;
		setId(ID);
	}

	@Override
	public void run() {
		final LinkedList<Point> newList = new LinkedList<Point>();
		for (int i = 0; i < featureModel.getConstraints().size(); i++) {
			newList.add(featureModel.getConstraints().get(i).getLocation());
		}
		final int counter = oldPos.size();
		oldPos.add(newList);
		final AutoLayoutConstraintOperation op = new AutoLayoutConstraintOperation(featureModel, oldPos, counter);
		// TODO _interfaces Removed Code
		op.addContext((IUndoContext) featureModel.getFeatureModel().getUndoContext());

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);

		}
	}

}
