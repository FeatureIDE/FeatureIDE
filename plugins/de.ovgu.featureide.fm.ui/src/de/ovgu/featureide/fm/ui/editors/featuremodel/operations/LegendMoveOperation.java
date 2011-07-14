/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.AbstractOperation;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;

/**
 * Operation to move the Legend. Provides undo/redo functionality.
 * 
 * @author Fabian Benduhn
 */
public class LegendMoveOperation extends AbstractOperation {

	private static final String LABEL = "Move Legend";
	private FeatureModel featureModel;
	private Point pos;
	private org.eclipse.draw2d.geometry.Point oldPos;
	private boolean wasAutoLayout;
	private LegendFigure figure;


	public LegendMoveOperation(FeatureModel featureModel,
			org.eclipse.draw2d.geometry.Point p, Point newPos, LegendFigure figure) {
		super(LABEL);
		this.featureModel = featureModel;
		this.pos = p;
		this.figure = figure;
		this.oldPos = new Point(featureModel.getLegendPos().x,
				featureModel.getLegendPos().y);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.operations.AbstractOperation#execute(org.eclipse
	 * .core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus execute(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
	
		this.wasAutoLayout = featureModel.hasLegendAutoLayout();
		return redo(monitor, info);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.operations.AbstractOperation#redo(org.eclipse
	 * .core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus redo(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		figure=FeatureUIHelper.getLegendFigure();
		figure.setLocation(pos);
		featureModel.setLegendPos(pos.x, pos.y);
		featureModel.setLegendAutoLayout(false);
		featureModel.refreshContextMenu();
	//	featureModel.handleModelDataChanged();
		//featureModel.redrawDiagram();
		return Status.OK_STATUS;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.operations.AbstractOperation#undo(org.eclipse
	 * .core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus undo(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {

		featureModel.setLegendPos(oldPos.x, oldPos.y);
		featureModel.setLegendAutoLayout(wasAutoLayout);
		featureModel.redrawDiagram();
		featureModel.refreshContextMenu();
		return Status.OK_STATUS;
	}

}
