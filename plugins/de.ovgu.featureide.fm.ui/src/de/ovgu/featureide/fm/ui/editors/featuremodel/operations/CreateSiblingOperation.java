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

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_SIBLING;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFAULT_FEATURE_LAYER_CAPTION;

import java.util.LinkedList;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * TODO description
 *
 * @author Sabrina Hugo
 * @author Christian Orsinger
 */
public class CreateSiblingOperation extends AbstractFeatureModelOperation {

	IGraphicalFeatureModel featureModel;
	LinkedList<IFeature> selectedFeatures;
	IFeature newCompound;

	public CreateSiblingOperation(IGraphicalFeatureModel featureModel, LinkedList<IFeature> selectedFeatures) {
		super(featureModel.getFeatureModel(), CREATE_SIBLING);
		this.selectedFeatures = selectedFeatures;
		this.featureModel = featureModel;
		int number = 0;
		while (FeatureUtils.getFeatureNames(featureModel.getFeatureModel()).contains(DEFAULT_FEATURE_LAYER_CAPTION + ++number)) {}

		newCompound =
			FMFactoryManager.getFactory(featureModel.getFeatureModel()).createFeature(featureModel.getFeatureModel(), DEFAULT_FEATURE_LAYER_CAPTION + number);
		System.out.println("Das hier passiert, wenn man auf CreateSibling drückt: " + newCompound.getName());
	}

	@Override
	protected FeatureIDEEvent operation() {
		final IFeatureStructure parent = selectedFeatures.get(0).getStructure().getParent();
		if (parent != null) {
			parent.addChild(newCompound.getStructure());
			featureModel.getFeatureModel().addFeature(newCompound);
		} else {
			return null;
		}

		return new FeatureIDEEvent(featureModel, EventType.FEATURE_ADD_SIBLING, parent != null ? parent.getFeature() : null, newCompound);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		newCompound = featureModel.getFeatureModel().getFeature(newCompound.getName());
		featureModel.getFeatureModel().deleteFeature(newCompound);
		return new FeatureIDEEvent(newCompound, EventType.FEATURE_DELETE, null, newCompound);
	}
}
