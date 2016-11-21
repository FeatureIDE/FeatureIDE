/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_COMPOUND;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFAULT_FEATURE_LAYER_CAPTION;

import java.util.Collections;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.Feature;

/**
 * Operation with functionality to create a compound feature. Enables undo/redo
 * functionality.
 * 
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class CreateFeatureAboveOperation extends AbstractFeatureModelOperation {

	private final IFeature newCompound;
	private final IFeature child;

	public CreateFeatureAboveOperation(IFeatureModel featureModel, IFeature selectedFeature) {
		super(featureModel, CREATE_COMPOUND);
		this.child = selectedFeature;
		
		int number = 0;
		while (FeatureUtils.getFeatureNames(featureModel).contains(DEFAULT_FEATURE_LAYER_CAPTION + ++number)){}
		
		newCompound = new Feature(featureModel, DEFAULT_FEATURE_LAYER_CAPTION + number);
	}

	@Override
	protected FeatureIDEEvent operation() {
		IFeatureStructure parent = child.getStructure().getParent();
		if (parent != null) {
			newCompound.getStructure().setAND(true);
			newCompound.getStructure().setMultiple(parent.isMultiple());
		}
		
		if (parent != null) {
			final int index = parent.getChildIndex(child.getStructure());
			parent.removeChild(child.getStructure());
			parent.addChildAtPosition(index, newCompound.getStructure());
			newCompound.getStructure().addChild(child.getStructure());
			featureModel.addFeature(newCompound);
		} else {
			newCompound.getStructure().addChild(child.getStructure());
			featureModel.addFeature(newCompound);
			featureModel.getStructure().setRoot(newCompound.getStructure());
		}
		return new FeatureIDEEvent(featureModel, EventType.FEATURE_ADD_ABOVE, parent != null ? parent.getFeature() : null, newCompound);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		final IFeatureStructure parent = newCompound.getStructure().getParent();
		if (parent != null) {
			parent.addChildAtPosition(parent.getChildIndex(newCompound.getStructure()), child.getStructure());
		}
		newCompound.getStructure().setChildren(Collections.<IFeatureStructure>emptyList());
		featureModel.deleteFeature(newCompound);
		if (parent == null) {
			featureModel.getStructure().replaceRoot(child.getStructure());
			return new FeatureIDEEvent(newCompound, EventType.FEATURE_DELETE, null, null);
		}
		return new FeatureIDEEvent(newCompound, EventType.FEATURE_DELETE, parent.getFeature(), null);
	}

}
