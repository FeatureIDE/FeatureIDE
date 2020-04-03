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

import static de.ovgu.featureide.fm.core.localization.StringTable.DEFAULT_FEATURE_LAYER_CAPTION;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation with functionality to create a layer feature. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Sebastian Krieter
 */
public class CreateFeatureOperation extends AbstractFeatureModelOperation {

	private final String parentName;
	private String newFeatureName;
	private final int index;

	public CreateFeatureOperation(String parentName, int index, IFeatureModelManager featureModelManager) {
		super(featureModelManager, "Create Feature");
		this.parentName = parentName;
		this.index = index;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		newFeatureName = FeatureUtils.getFeatureName(featureModel, DEFAULT_FEATURE_LAYER_CAPTION);
		final IFeature newFeature = FMFactoryManager.getInstance().getFactory(featureModel).createFeature(featureModel, newFeatureName);
		featureModel.addFeature(newFeature);
		final IFeature parent = featureModel.getFeature(parentName);
		parent.getStructure().addChildAtPosition(index, newFeature.getStructure());
		return new FeatureIDEEvent(featureModel, EventType.FEATURE_ADD, null, newFeature);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IFeature newFeature = featureModel.getFeature(newFeatureName);
		featureModel.deleteFeature(newFeature);
		return new FeatureIDEEvent(newFeature, EventType.FEATURE_DELETE, null, newFeature);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
