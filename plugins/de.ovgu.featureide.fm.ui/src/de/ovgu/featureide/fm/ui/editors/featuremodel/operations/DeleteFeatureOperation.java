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

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE;

import java.util.LinkedList;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Operation to delete a feature from the model.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class DeleteFeatureOperation extends AbstractFeatureModelOperation {

	private IFeature feature;
	private IFeature oldParent;
	private int oldIndex;
	private LinkedList<IFeature> oldChildren;
	private boolean deleted = false;
	private boolean or = false;
	private boolean alternative = false;
	private final IFeature replacement;

	public DeleteFeatureOperation(IFeatureModel featureModel, IFeature feature) {
		super(featureModel, DELETE);
		this.feature = feature;
		replacement = null;
	}

	public DeleteFeatureOperation(IFeatureModel featureModel, IFeature feature, IFeature replacement) {
		super(featureModel, DELETE);
		this.feature = feature;
		this.replacement = replacement;
	}

	@Override
	protected FeatureIDEEvent operation() {
		feature = featureModel.getFeature(feature.getName());
		oldParent = FeatureUtils.getParent(feature);
		if (oldParent != null) {
			oldIndex = oldParent.getStructure().getChildIndex(feature.getStructure());
			or = oldParent.getStructure().isOr();
			alternative = oldParent.getStructure().isAlternative();
		}
		oldChildren = new LinkedList<IFeature>();
		oldChildren.addAll(Functional.toList(FeatureUtils.convertToFeatureList(feature.getStructure().getChildren())));

		if (oldParent != null) {
			oldParent = featureModel.getFeature(oldParent.getName());
		}
		final LinkedList<IFeature> oldChildrenCopy = new LinkedList<IFeature>();

		for (final IFeature f : oldChildren) {
			if (!f.getName().equals(feature.getName())) {
				final IFeature oldChild = featureModel.getFeature(f.getName());
				oldChildrenCopy.add(oldChild);
			}
		}

		oldChildren = oldChildrenCopy;
		if (feature.getStructure().isRoot()) {
			featureModel.getStructure().replaceRoot(featureModel.getStructure().getRoot().removeLastChild());
			deleted = true;
		} else {
			deleted = featureModel.deleteFeature(feature);
		}

		// Replace feature name in constraints
		if (replacement != null) {
			for (final IConstraint c : featureModel.getConstraints()) {
				if (c.getContainedFeatures().contains(feature)) {
					c.getNode().replaceFeature(feature, replacement);
				}
			}
		}

		// make sure after delete the group type of the parent is set to and if there is only one child left
		if (oldParent != null) {
			if (oldParent.getStructure().getChildrenCount() == 1) {
				oldParent.getStructure().changeToAnd();
			}
		}
		return new FeatureIDEEvent(feature, EventType.FEATURE_DELETE, oldParent, null);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		try {
			if (!deleted) {
				return null;
			}

			if (oldParent != null) {
				oldParent = featureModel.getFeature(oldParent.getName());
			}
			final LinkedList<IFeature> oldChildrenCopy = new LinkedList<IFeature>();

			for (final IFeature f : oldChildren) {
				if (!f.getName().equals(feature.getName())) {
					final IFeature child = featureModel.getFeature(f.getName());
					if ((child != null) && (child.getStructure().getParent() != null)) {
						child.getStructure().getParent().removeChild(child.getStructure());
					}
					oldChildrenCopy.add(child);
				}
			}

			oldChildren = oldChildrenCopy;

			feature.getStructure().setChildren(Functional.toList(FeatureUtils.convertToFeatureStructureList(oldChildren)));
			if (oldParent != null) {
				oldParent.getStructure().addChildAtPosition(oldIndex, feature.getStructure());
			} else {
				featureModel.getStructure().setRoot(feature.getStructure());
			}
			featureModel.addFeature(feature);

			// Replace feature name in Constraints
			if (replacement != null) {
				for (final IConstraint c : featureModel.getConstraints()) {
					if (c.getContainedFeatures().contains(replacement)) {
						c.getNode().replaceFeature(replacement, feature);
					}
				}
			}

			// When deleting a child and leaving one child behind the group type will be changed to and. reverse to old group type
			if ((oldParent != null) && or) {
				oldParent.getStructure().changeToOr();
			} else if ((oldParent != null) && alternative) {
				oldParent.getStructure().changeToAlternative();
			}

		} catch (final Exception e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return new FeatureIDEEvent(featureModel, EventType.FEATURE_ADD, feature, feature);
	}

	@Override
	public boolean canUndo() {
		return (oldParent == null) || (featureModel.getFeature(oldParent.getName()) != null);
	}
}
