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

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE;

import java.util.Collections;
import java.util.LinkedList;
import java.util.Optional;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Operation to delete a single feature from the model.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 * @author Benedikt Jutz
 */
public class DeleteFeatureOperation extends AbstractFeatureModelOperation {

	public static final String ID = ID_PREFIX + "DeleteFeatureOperation";

	private final LinkedList<String> oldChildrenNames = new LinkedList<>();
	private final String featureName;
	private final String replacementName;

	private IFeature oldFeature;
	private String oldParentName;
	private int oldIndex;
	private boolean deleted;
	private boolean or;
	private boolean alternative;

	private boolean isMandatory;

	public DeleteFeatureOperation(IFeatureModelManager featureModelManger, String featureName, boolean isMandatory) {
		this(featureModelManger, featureName, null);
		this.isMandatory = isMandatory;
	}

	public DeleteFeatureOperation(IFeatureModelManager featureModelManger, String featureName, String replacementName) {
		super(featureModelManger, DELETE);
		this.featureName = featureName;
		this.replacementName = replacementName;
	}

	/**
	 * Disallow <code>operation</code>/deletion of <code>featureName</code> if it appears in an constraint of another model.
	 *
	 * @see {@link AbstractFeatureModelOperation#approveRedo()}
	 */
	@Override
	protected Optional<String> approveRedo() {
		final IFeatureModel model = featureModelManager.getVarObject();
		if (ElementDeleteOperation.testForFeatureReferences(featureModelManager, model, Collections.singletonList(model.getFeature(featureName)))) {
			return Optional.of(StringTable.AT_LEAST_ONE_FEATURE_APPEARS_IN_A_CONSTRAINT_IN_ANOTHER_FEATURE_MODEL);
		} else {
			return Optional.empty();
		}
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		oldFeature = featureModel.getFeature(featureName);
		// Save data about the old parent (name, index, group type).
		final IFeature oldParent = FeatureUtils.getParent(oldFeature);
		if (oldParent != null) {
			oldParentName = oldParent.getName();
			oldIndex = oldParent.getStructure().getChildIndex(oldFeature.getStructure());
			or = oldParent.getStructure().isOr();
			alternative = oldParent.getStructure().isAlternative();
		}

		// Save old child names.
		final Iterable<IFeature> oldChildren = FeatureUtils.getChildren(oldFeature);
		oldChildrenNames.clear();
		oldChildrenNames.addAll(Functional.mapToStringList(oldChildren));

		// Should oldFeature be the (former) root feature, replace it with its last child.
		if (oldFeature.getStructure().isRoot()) {
			if (oldFeature.getStructure().getChildrenCount() == 1) {
				oldFeature.getStructure().getChildren().get(0).setMandatory(isMandatory);
			}
			featureModel.getStructure().replaceRoot(featureModel.getStructure().getRoot().removeLastChild());
			deleted = true;
		} else {
			deleted = featureModel.deleteFeature(oldFeature);
		}

		// Replace feature name in constraints.
		if (replacementName != null) {
			for (final IConstraint c : featureModel.getConstraints()) {
				c.getNode().replaceFeature(featureName, replacementName);
			}
		}

		// Ensure after deletion that the group type of the parent is set to and if there is only one child left.
		if (oldParent != null) {
			if (oldParent.getStructure().getChildrenCount() == 1) {
				oldParent.getStructure().changeToAnd();
			}
		}

		return new FeatureModelOperationEvent(ID, EventType.FEATURE_DELETE, oldFeature, oldParent, featureModel);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		try {
			if (!deleted) {
				return null;
			}

			final IFeature oldParent = (oldParentName != null) ? featureModel.getFeature(oldParentName) : null;

			final LinkedList<IFeature> oldChildren = new LinkedList<>();
			for (final String name : oldChildrenNames) {
				final IFeature child = featureModel.getFeature(name);
				oldChildren.add(child);
				final IFeatureStructure structure = child.getStructure();
				if (structure.getParent() != null) {
					structure.getParent().removeChild(structure);
				}
			}

			final IFeature feature = FMFactoryManager.getInstance().getFactory(featureModel).copyFeature(featureModel, oldFeature);
			feature.getStructure().setChildren(FeatureUtils.convertToFeatureStructureList(oldChildren));
			if (oldParent != null) {
				oldParent.getStructure().addChildAtPosition(oldIndex, feature.getStructure());
			} else {
				featureModel.getStructure().setRoot(feature.getStructure());
			}
			featureModel.addFeature(feature);

			// Replace feature name in Constraints
			if (replacementName != null) {
				for (final IConstraint c : featureModel.getConstraints()) {
					c.getNode().replaceFeature(replacementName, featureName);
				}
			}

			// When deleting a child the parent's group type may be changed (to and when leaving one sibling behind, to the child's group type when leaving no
			// siblings behind). Reverse to old group type.
			if (oldParent != null) {
				if (or) {
					oldParent.getStructure().changeToOr();
				} else if (alternative) {
					oldParent.getStructure().changeToAlternative();
				} else {
					oldParent.getStructure().changeToAnd();
				}
			}

			return new FeatureModelOperationEvent(ID, EventType.FEATURE_ADD, featureModel, oldParent, feature);
		} catch (final Exception e) {
			FMUIPlugin.getDefault().logError(e);
			return null;
		}
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
