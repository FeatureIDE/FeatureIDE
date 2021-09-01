/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
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
public class SetFeatureToCollapseOperation extends ComposedFeatureModelOperation {

	public static final String ID = ID_PREFIX + "SetFeatureToCollapseOperation";

	private final IGraphicalFeatureModel graphicalFeatureModel;

	private final boolean allCollapsed;
	private final String operationLabel;

	public SetFeatureToCollapseOperation(List<String> featureNames, IGraphicalFeatureModel graphicalFeatureModel, boolean allCollapsed, String operationLabel) {
		super(graphicalFeatureModel.getFeatureModelManager(), operationLabel, featureNames);
		this.graphicalFeatureModel = graphicalFeatureModel;
		this.allCollapsed = allCollapsed;
		this.operationLabel = operationLabel;
	}

	@Override
	protected String getID() {
		return ID;
	}

	@Override
	protected void createSingleOperations(IFeatureModel featureModel) {
		for (final String name : featureNames) {
			final IFeature tempFeature = featureModel.getFeature(name);
			if (allCollapsed || !graphicalFeatureModel.getGraphicalFeature(tempFeature).isCollapsed()) {
				final CollapseFeatureOperation op = new CollapseFeatureOperation(name, graphicalFeatureModel, operationLabel);
				operations.add(op);
			}
		}
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_GRAPHICS;
	}

}
