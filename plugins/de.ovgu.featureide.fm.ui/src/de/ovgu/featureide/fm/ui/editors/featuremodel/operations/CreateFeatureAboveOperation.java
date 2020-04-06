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
import java.util.LinkedList;
import java.util.Map.Entry;
import java.util.TreeMap;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation with functionality to create a compound feature. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class CreateFeatureAboveOperation extends AbstractFeatureModelOperation {

	private final String childName;
	private final LinkedList<String> selectedFeatureNames;
	private final TreeMap<Integer, String> children = new TreeMap<>();

	private String featureName;

	boolean parentOr = false;
	boolean parentAlternative = false;

	public CreateFeatureAboveOperation(IFeatureModelManager featureModelManager, LinkedList<String> selectedFeatures) {
		super(featureModelManager, "Add Feature");
		selectedFeatureNames = selectedFeatures;
		childName = selectedFeatures.get(0);
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		featureName = FeatureUtils.getFeatureName(featureModel, DEFAULT_FEATURE_LAYER_CAPTION);
		children.clear();
		final IFeature newFeature = FMFactoryManager.getInstance().getFactory(featureModel).createFeature(featureModel, featureName);
		final IFeature child = featureModel.getFeature(childName);
		final IFeatureStructure parent = child.getStructure().getParent();
		if (parent != null) {
			parentOr = parent.isOr();
			parentAlternative = parent.isAlternative();

			newFeature.getStructure().setMultiple(parent.isMultiple());
			final int index = parent.getChildIndex(child.getStructure());
			for (final String name : selectedFeatureNames) {
				final IFeature iFeature = featureModel.getFeature(name);
				children.put(parent.getChildIndex(iFeature.getStructure()), iFeature.getName());
				parent.removeChild(iFeature.getStructure());
			}
			parent.addChildAtPosition(index, newFeature.getStructure());
			for (final String name : selectedFeatureNames) {
				newFeature.getStructure().addChild(featureModel.getFeature(name).getStructure());
			}

			if (parentOr) {
				newFeature.getStructure().changeToOr();
			} else if (parentAlternative) {
				newFeature.getStructure().changeToAlternative();
			} else {
				newFeature.getStructure().changeToAnd();
			}
			parent.changeToAnd();
			featureModel.addFeature(newFeature);
		} else {
			newFeature.getStructure().addChild(child.getStructure());
			featureModel.addFeature(newFeature);
			featureModel.getStructure().setRoot(newFeature.getStructure());
		}
		return new FeatureIDEEvent(featureModel, EventType.FEATURE_ADD_ABOVE, parent != null ? parent.getFeature() : null, newFeature);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IFeature newFeature = featureModel.getFeature(featureName);
		final IFeature child = featureModel.getFeature(childName);
		final IFeatureStructure parent = newFeature.getStructure().getParent();
		if (parent != null) {
			newFeature.getStructure().setChildren(Collections.<IFeatureStructure> emptyList());
			featureModel.deleteFeature(newFeature);
			for (final Entry<Integer, String> childEntry : children.entrySet()) {
				parent.addChildAtPosition(childEntry.getKey(), featureModel.getFeature(childEntry.getValue()).getStructure());
			}

			if (parentOr) {
				parent.changeToOr();
			} else if (parentAlternative) {
				parent.changeToAlternative();
			} else {
				parent.changeToAnd();
			}
		} else {
			featureModel.getStructure().replaceRoot(child.getStructure());
			newFeature.getStructure().removeChild(child.getStructure());
			return new FeatureIDEEvent(newFeature, EventType.FEATURE_DELETE, null, null);
		}
		return new FeatureIDEEvent(newFeature, EventType.FEATURE_DELETE, parent.getFeature(), null);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
