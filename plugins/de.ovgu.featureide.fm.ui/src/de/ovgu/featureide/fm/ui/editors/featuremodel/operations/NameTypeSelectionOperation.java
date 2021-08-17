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

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutHelper;

/**
 * Operation that chooses the type of name labels (short or long ones) for MultiFeatureModels.
 *
 * @author Reimar Schroeter
 * @author Sebastian Krieter
 * @author Benedikt Jutz
 */
public class NameTypeSelectionOperation extends AbstractGraphicalFeatureModelOperation {

	/**
	 * Specifies if either short or long labels should be used.
	 */
	private final boolean useShortLabels;

	public NameTypeSelectionOperation(IGraphicalFeatureModel graphicalFeatureModel, boolean useShortLabels) {
		super(graphicalFeatureModel, FeatureDiagramLayoutHelper.getNameTypeLabel(useShortLabels));
		this.useShortLabels = useShortLabels;
	}

	/**
	 * Sets the short labels property of the garphical feature model to useShortLabels, and then returns an ALL_FEATURES_CHANGED_NAME_TYPE event to trigger the
	 * display of the new names.
	 *
	 * @see {@link AbstractFeatureModelOperation#operation(IFeatureModel)}
	 */
	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		graphicalFeatureModel.getLayout().setShowShortNames(useShortLabels);
		return FeatureIDEEvent.getDefault(EventType.ALL_FEATURES_CHANGED_NAME_TYPE);
	}

	/**
	 * Works like inverseOperation, but setw the short labels property to !useShortLabels.
	 *
	 * @see {@link AbstractFeatureModelOperation#inverseOperation(IFeatureModel)}
	 */
	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		graphicalFeatureModel.getLayout().setShowShortNames(!useShortLabels);
		return FeatureIDEEvent.getDefault(EventType.ALL_FEATURES_CHANGED_NAME_TYPE);
	}

}
