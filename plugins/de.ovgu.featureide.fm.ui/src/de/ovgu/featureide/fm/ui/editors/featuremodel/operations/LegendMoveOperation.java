/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelLayout;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;

/**
 * Operation to move the Legend. Provides undo/redo functionality.
 * 
 * @author Fabian Benduhn
 */
public class LegendMoveOperation extends AbstractFeatureModelOperation {

	private static final String LABEL = "Move Legend";
	private Point newLocation;
	private Point oldLocation;
	private boolean wasAutoLayout;

	public LegendMoveOperation(FeatureModel featureModel, Point newLocation, LegendFigure legendFigure) {
		super(featureModel, LABEL);
		this.newLocation = newLocation;
		this.oldLocation = legendFigure.getLocation();
	}
	
	@Override
	public IStatus execute(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		this.wasAutoLayout = featureModel.getLayout().hasLegendAutoLayout();
		return redo(monitor, info);
	}

	@Override
	protected void redo() {
		FeatureUIHelper.getLegendFigure(featureModel).setLocation(newLocation);
		final FeatureModelLayout layout = featureModel.getLayout();
		layout.setLegendPos(newLocation.x, newLocation.y);
		layout.setLegendAutoLayout(false);
		featureModel.handleLegendLayoutChanged(); 
	}

	@Override
	protected void undo() {
		FeatureUIHelper.getLegendFigure(featureModel).setLocation(oldLocation);
		final FeatureModelLayout layout = featureModel.getLayout();
		layout.setLegendPos(oldLocation.x, oldLocation.y);
		layout.setLegendAutoLayout(wasAutoLayout);
		featureModel.handleLegendLayoutChanged(); 
	}

}
