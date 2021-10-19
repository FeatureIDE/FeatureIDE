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
import java.util.List;
import java.util.Map.Entry;
import java.util.TreeMap;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.IMultiFeatureModelElement;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation with functionality to create a compound feature. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class CreateFeatureAboveOperation extends AbstractFeatureModelOperation {

	/**
	 * Contains the names of the features for whom we create a new parent feature.
	 */
	private final List<String> selectedFeatureNames;
	/**
	 * <code>childName</code> is the name of the first selected feature name.
	 */
	private final String childName;
	/**
	 * <code>children</code> stores the old positions and names for selectedFeatures to run <code>inverseOperation</code> correctly.
	 */
	private final TreeMap<Integer, String> children = new TreeMap<>();

	/**
	 * <code>featureName</code> contains the name of the new parent feature.
	 */
	private String featureName;
	/**
	 * Declares whether this action occurs from an imported/referenced model, or not,
	 */
	private final boolean createAsImport;
	/**
	 * Stores whether the parent of the feature <code>childName</code> has an or group.
	 */
	private boolean parentOr = false;
	/**
	 * Stores whether the parent of the feature <code>childName</code> has an alternative group.
	 */
	private boolean parentAlternative = false;
	/**
	 * Stores whether the
	 */
	private boolean needToUpdateMandatory = false;

	/**
	 * Creates a new {@link CreateFeatureAboveOperation}.
	 *
	 * @param featureModelManager - {@link IFeatureModelManager}
	 * @param selectedFeatureNames - {@link List}
	 */
	public CreateFeatureAboveOperation(IFeatureModelManager featureModelManager, List<String> selectedFeatureNames) {
		super(featureModelManager, "Add Feature");
		this.selectedFeatureNames = selectedFeatureNames;
		childName = selectedFeatureNames.get(0);
		createAsImport = false;
	}

	/**
	 * Creates a new {@link CreateFeatureAboveOperation} for imported features.
	 *
	 * @param featureModelManager - {@link IFeatureModelManager}
	 * @param selectedFeatureNames - {@link List}
	 * @param featureName - {@link String}
	 * @param needToUpdateMandatory - {@link Boolean}
	 */
	public CreateFeatureAboveOperation(IFeatureModelManager featureModelManager, List<String> selectedFeatureNames, String featureName,
			boolean needToUpdateMandatory) {
		super(featureModelManager, "Add Feature");
		this.selectedFeatureNames = selectedFeatureNames;
		childName = selectedFeatureNames.get(0);
		createAsImport = true;
		this.featureName = featureName;
		this.needToUpdateMandatory = needToUpdateMandatory;
	}

	/**
	 * Creates a new feature with the given <code>featureName</code>. For an import, mark this {@link MultiFeature} as interface and do not create a new name.
	 * <br> The new feature takes the group type of the previous parent of the features named in <code>selectedFeatures</code>, and has them as children. The
	 * old parent loses those children, and its type is converted into an AND.
	 *
	 * @return new {@link FeatureIDEEvent} with {@link EventType#FEATURE_ADD_ABOVE} as type.
	 */
	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		featureName = (!createAsImport) ? FeatureUtils.getFeatureName(featureModel, DEFAULT_FEATURE_LAYER_CAPTION) : featureName;
		children.clear();
		final IFeature newFeature = FMFactoryManager.getInstance().getFactory(featureModel).createFeature(featureModel, featureName);
		if (createAsImport) {
			final MultiFeature multiFeature = (MultiFeature) newFeature;
			multiFeature.setType(IMultiFeatureModelElement.TYPE_INTERFACE);
		}

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
				if (needToUpdateMandatory) {
					newFeature.getStructure().setMandatory(true);
				}
			}
			parent.changeToAnd();
			if (needToUpdateMandatory) {
				child.getStructure().setMandatory(false);
			}
			featureModel.addFeature(newFeature);
		} else {
			newFeature.getStructure().addChild(child.getStructure());
			featureModel.addFeature(newFeature);
			featureModel.getStructure().setRoot(newFeature.getStructure());
		}

		return new FeatureIDEEvent(featureModel, EventType.FEATURE_ADD_ABOVE,
				new Object[] { parent != null ? parent.getFeature() : null, selectedFeatureNames }, newFeature);
	}

	/**
	 * Deletes the feature named with <code>featureName</code>, and converts the group type of its parent as saved in <code>parentOr/parentAlternative</code>.
	 * Also adds the previous features back at the right indexes, according to the entries in <code>children</code>.
	 *
	 * @return new {@link FeatureIDEEvent} with {@link EventType#FEATURE_DELETE} as type.
	 * @see {@link CreateFeatureAboveOperation#operation(IFeatureModel)} for the creation of <code>children/parentAlternative/parentOr</code>.
	 */
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
				if (needToUpdateMandatory) {
					child.getStructure().setMandatory(true);
				}
			}
			return new FeatureIDEEvent(newFeature, EventType.FEATURE_DELETE, parent.getFeature(), null);
		} else {
			featureModel.getStructure().replaceRoot(child.getStructure());
			newFeature.getStructure().removeChild(child.getStructure());
			return new FeatureIDEEvent(newFeature, EventType.FEATURE_DELETE, null, null);
		}
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
