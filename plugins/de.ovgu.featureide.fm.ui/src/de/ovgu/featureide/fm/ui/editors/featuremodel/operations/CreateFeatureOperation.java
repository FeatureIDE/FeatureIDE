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

import java.util.Collections;
import java.util.Optional;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IMultiFeatureModelElement;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * Operation with functionality to create a layer feature. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Sebastian Krieter
 */
public class CreateFeatureOperation extends AbstractFeatureModelOperation {

	private final String parentName;
	private String newFeatureName;
	private final boolean createAsImport;
	private final int index;

	public CreateFeatureOperation(String parentName, int index, IFeatureModelManager featureModelManager) {
		super(featureModelManager, StringTable.CREATE_FEATURE);
		this.parentName = parentName;
		this.index = index;
		createAsImport = false;
	}

	public CreateFeatureOperation(String parentName, String childName, int index, IFeatureModelManager manager) {
		super(manager, StringTable.CREATE_FEATURE);
		this.parentName = parentName;
		newFeatureName = childName;
		this.index = index;
		createAsImport = true;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		newFeatureName = (newFeatureName == null) ? FeatureUtils.getFeatureName(featureModel, DEFAULT_FEATURE_LAYER_CAPTION) : newFeatureName;
		final IFeature newFeature = FMFactoryManager.getInstance().getFactory(featureModel).createFeature(featureModel, newFeatureName);
		featureModel.addFeature(newFeature);
		final IFeature parent = featureModel.getFeature(parentName);
		parent.getStructure().addChildAtPosition(index, newFeature.getStructure());
		if (createAsImport) {
			// Finally mark the feature as imported from an interface.
			final MultiFeature multiFeature = (MultiFeature) newFeature;
			multiFeature.setType(IMultiFeatureModelElement.TYPE_INTERFACE);
		}
		return new FeatureIDEEvent(featureModel, EventType.FEATURE_ADD, parent, newFeature);
	}

	/**
	 * Disallow <code>inverseOperation</code>/deletion of <code>featureName</code> if it appears in an constraint of another model.
	 */
	@Override
	protected Optional<String> approveUndo() {
		final IFeatureModel model = featureModelManager.getVarObject();
		if (ElementDeleteOperation.testForFeatureReferences(featureModelManager, model, Collections.singletonList(model.getFeature(newFeatureName)))) {
			return Optional.of(StringTable.AT_LEAST_ONE_FEATURE_APPEARS_IN_A_CONSTRAINT_IN_ANOTHER_FEATURE_MODEL);
		} else {
			return Optional.empty();
		}
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
