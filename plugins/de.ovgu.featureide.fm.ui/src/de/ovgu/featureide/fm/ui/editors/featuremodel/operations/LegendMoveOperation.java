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

import static de.ovgu.featureide.fm.core.localization.StringTable.MOVE_LEGEND;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;

/**
 * Operation to move the Legend. Provides undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class LegendMoveOperation extends AbstractGraphicalFeatureModelOperation {

	private final LegendFigure legendFigure;
	private final Point newLocation;

	private Point oldLocation;
	private boolean wasAutoLayout;

	public LegendMoveOperation(IGraphicalFeatureModel featureModel, Point newLocation, LegendFigure legendFigure) {
		super(featureModel, MOVE_LEGEND);
		this.newLocation = newLocation;
		this.legendFigure = legendFigure;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		oldLocation = legendFigure.getLocation();
		legendFigure.setLocation(newLocation);
		graphicalFeatureModel.getLegend().setPos(newLocation);
		wasAutoLayout = graphicalFeatureModel.getLayout().hasLegendAutoLayout();
		graphicalFeatureModel.getLayout().setLegendAutoLayout(false);
		graphicalFeatureModel.handleLegendLayoutChanged();
		return new FeatureIDEEvent(true, EventType.LEGEND_LAYOUT_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		legendFigure.setLocation(oldLocation);
		graphicalFeatureModel.getLegend().setPos(oldLocation);
		graphicalFeatureModel.getLayout().setLegendAutoLayout(wasAutoLayout);
		graphicalFeatureModel.handleLegendLayoutChanged();
		return new FeatureIDEEvent(true, EventType.LEGEND_LAYOUT_CHANGED);
	}

}
