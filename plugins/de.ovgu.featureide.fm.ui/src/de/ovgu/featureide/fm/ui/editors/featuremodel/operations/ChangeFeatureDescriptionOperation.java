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

import static de.ovgu.featureide.fm.core.localization.StringTable.CHANGE_DESCRIPTION;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation to change a feature description. Enables undo/redo functionality.
 *
 * @author Johannes Herschel
 */
public class ChangeFeatureDescriptionOperation extends AbstractFeatureModelOperation {

	private final String featureName;

	private final String oldDescription;
	private final String newDescription;

	public ChangeFeatureDescriptionOperation(IFeatureModelManager featureModelManager, String featureName, String oldDescription, String newDescription) {
		super(featureModelManager, CHANGE_DESCRIPTION);
		this.featureName = featureName;
		this.oldDescription = oldDescription;
		this.newDescription = newDescription;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(featureName);
		feature.getProperty().setDescription(newDescription);
		return new FeatureIDEEvent(feature, EventType.ATTRIBUTE_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(featureName);
		feature.getProperty().setDescription(oldDescription);
		return new FeatureIDEEvent(feature, EventType.ATTRIBUTE_CHANGED);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_MODEL_PROPERTY;
	}
}
