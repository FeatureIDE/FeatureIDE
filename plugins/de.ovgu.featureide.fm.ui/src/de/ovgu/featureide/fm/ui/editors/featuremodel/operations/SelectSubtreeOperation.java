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

import static de.ovgu.featureide.fm.core.localization.StringTable.SELECT_SUBTREE;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation with functionality to select the whole subtree of a feature. Enables undo/redo functionality.
 *
 * @author Sabrina Hugo
 * @author Christian Orsinger
 */
public class SelectSubtreeOperation extends AbstractFeatureModelOperation {

	private final IFeature feature;
	private final IGraphicalFeatureModel graphicalFeatureModel;

	/**
	 * @param featureModel
	 * @param label
	 */
	public SelectSubtreeOperation(IFeature feature, IGraphicalFeatureModel featureModel) {
		super(featureModel.getFeatureModel(), SELECT_SUBTREE);
		this.feature = feature;
		graphicalFeatureModel = featureModel;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation#operation()
	 */
	@Override
	protected FeatureIDEEvent operation() {
		graphicalFeatureModel.getGraphicalFeature(feature).isConstraintSelected()
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation#inverseOperation()
	 */
	@Override
	protected FeatureIDEEvent inverseOperation() {
		// TODO Auto-generated method stub
		return null;
	}

}
