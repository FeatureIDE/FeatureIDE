/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import java.util.LinkedList;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 *
 * 
 * @author Fabian Benduhn
 */
public class FeatureDeleteOperation extends AbstractFeatureModelOperation {

	private Feature feature;
	private Feature oldParent;
	private int oldIndex;
	private LinkedList<Feature> oldChildren;
	private boolean deleted = false;
	private Feature replacement;

	public FeatureDeleteOperation(FeatureModel featureModel, Feature feature) {
		super(featureModel, "Delete");
		this.feature = feature;
		this.replacement = null;
	}
	
	public FeatureDeleteOperation(FeatureModel featureModel, Feature feature, Feature replacement) {
		super(featureModel, "Delete");
		this.feature = feature;
		this.replacement = replacement;
	}

	@Override
	protected void redo() {
		feature = featureModel.getFeature(feature.getName());
		oldParent = feature.getParent();
		if (oldParent != null) {
			oldIndex = oldParent.getChildIndex(feature);
		}
		oldChildren = new LinkedList<Feature>();
		oldChildren.addAll(feature.getChildren());

		if (oldParent != null) {
			oldParent = featureModel.getFeature(oldParent.getName());
		}
		LinkedList<Feature> oldChildrenCopy = new LinkedList<Feature>();

		for (Feature f : oldChildren) {
			if (!f.getName().equals(feature.getName())) {
				Feature oldChild = featureModel.getFeature(f.getName());
				oldChildrenCopy.add(oldChild);
			}
		}
		
		oldChildren = oldChildrenCopy;
		if (feature == featureModel.getRoot()) {
			featureModel.replaceRoot(featureModel.getRoot().removeLastChild());
			deleted = true;
		} else {
			deleted = featureModel.deleteFeature(feature);
		}
		
		//Replace feature name in constraints
		if (replacement != null) {
			for (Constraint c : featureModel.getConstraints()) {	
				if (c.getContainedFeatures().contains(feature)) {
					 c.getNode().replaceFeature(feature, replacement);
				}
			}			
		}
	}

	@Override
	protected void undo() {
		try {
			if (!deleted) {
				return;
			}
			
			if (oldParent != null) {
				oldParent = featureModel.getFeature(oldParent.getName());
			}
			LinkedList<Feature> oldChildrenCopy = new LinkedList<Feature>();

			for (Feature f : oldChildren) {
				if (!f.getName().equals(feature.getName())) {
					Feature child = featureModel.getFeature(f.getName());
					if (child != null && child.getParent() != null) {
						child.getParent().removeChild(child);
					}
					oldChildrenCopy.add(child);
				}
			}
			
			oldChildren = oldChildrenCopy;

			feature.setChildren(oldChildren);
			if (oldParent != null) {
				oldParent.addChildAtPosition(oldIndex, feature);
			} else {
				featureModel.setRoot(feature);
			}
			featureModel.addFeature(feature);
			
			//Replace Featurename in Constraints
			if (replacement != null) {
				for (Constraint c : featureModel.getConstraints()) {				
					if (c.getContainedFeatures().contains(replacement)) {
						 c.getNode().replaceFeature(replacement, feature);
					}
				}
			}
		} catch (Exception e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	@Override
	public boolean canUndo() {
		return oldParent == null || featureModel.getFeature(oldParent.getName()) != null;
	}
}
