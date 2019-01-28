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
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent;
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
public class CollapseFeatureOperation extends AbstractGraphicalFeatureModelOperation {

	public static final String ID = ID_PREFIX + "CollapseFeatureOperation";

	private final String featureName;
	private final List<FeatureConnection> targetConnections = new ArrayList<>();

	/**
	 * @param label Description of this operation to be used in the menu
	 * @param feature feature on which this operation will be executed
	 *
	 */
	public CollapseFeatureOperation(String featureName, IGraphicalFeatureModel graphicalFeatureModel, String operationLabel) {
		super(graphicalFeatureModel, operationLabel);
		this.featureName = featureName;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(featureName);
		targetConnections.clear();
		if (feature.getStructure().hasChildren()) {
			final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(feature);
			graphicalFeature.setCollapsed(!graphicalFeature.isCollapsed());
			targetConnections.addAll(graphicalFeature.getTargetConnections());
			graphicalFeature.getTargetConnections().clear();

			return new FeatureModelOperationEvent(ID, EventType.FEATURE_COLLAPSED_CHANGED, feature, null, null);
		}
		return new FeatureModelOperationEvent(ID, EventType.FEATURE_COLLAPSED_CHANGED, feature, null, null);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(featureName);
		if (feature.getStructure().hasChildren()) {
			graphicalFeatureModel.getGraphicalFeature(feature).getTargetConnections().addAll(targetConnections);
		}
		return operation(featureModel);
	}

}
