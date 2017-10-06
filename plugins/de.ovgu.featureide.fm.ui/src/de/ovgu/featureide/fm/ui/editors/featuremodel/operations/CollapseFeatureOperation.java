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

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.FeatureConnection;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation with functionality to set a feature to collapsed. Enables undo/redo functionality.
 *
 * @author Joshua Sprey
 * @author Enis Belli
 * @author Christopher Sontag
 * @author Chico Sundermann
 * @author Paul Westphal
 */
public class CollapseFeatureOperation extends AbstractFeatureModelOperation {

	private final IFeature feature;
	private final IGraphicalFeatureModel graphicalFeatureModel;
	private List<FeatureConnection> targetConnections = new ArrayList<>();

	/**
	 * @param label Description of this operation to be used in the menu
	 * @param feature feature on which this operation will be executed
	 *
	 */
	public CollapseFeatureOperation(IFeature feature, IGraphicalFeatureModel graphicalFeatureModel, String operationLabel) {
		super(graphicalFeatureModel.getFeatureModel(), operationLabel);
		this.graphicalFeatureModel = graphicalFeatureModel;
		this.feature = feature;
	}

	@Override
	protected FeatureIDEEvent operation() {
		if (feature.getStructure().hasChildren()) {
			final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(feature);
			graphicalFeature.setCollapsed(!graphicalFeature.isCollapsed());
			targetConnections = graphicalFeature.getTargetConnections();
			graphicalFeature.getTargetConnections().clear();

			return new FeatureIDEEvent(feature, EventType.COLLAPSED_CHANGED, null, null);
		}
		return new FeatureIDEEvent(feature, EventType.DEFAULT);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		if (feature.getStructure().hasChildren()) {
			graphicalFeatureModel.getGraphicalFeature(feature).getTargetConnections().addAll(targetConnections);
		}
		return operation();
	}

}