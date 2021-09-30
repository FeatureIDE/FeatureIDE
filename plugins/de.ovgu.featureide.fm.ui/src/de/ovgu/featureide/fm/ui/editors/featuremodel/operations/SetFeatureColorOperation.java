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

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * The operation to change the color of a feature. Enables redo and undo compatibility.
 *
 * @author Joshua Sprey
 */
public class SetFeatureColorOperation extends AbstractFeatureModelOperation {

	private final ArrayList<FeatureColor> oldColor = new ArrayList<>();
	/**
	 * Implicit property for each feature of this operation, before the operation is applied.
	 */
	private boolean[] implicitFeatures;

	private final FeatureColor newColor;
	private final List<String> featureNameList;

	public SetFeatureColorOperation(IFeatureModelManager featureModelManager, List<String> featureNameList, FeatureColor newColor) {
		super(featureModelManager, "Change feature color");
		this.featureNameList = featureNameList;
		this.newColor = newColor;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		oldColor.clear();
		implicitFeatures = new boolean[featureNameList.size()];
		final ArrayList<IFeature> featureList = new ArrayList<>(featureNameList.size());
		for (int i = 0; i < featureNameList.size(); i++) {
			final IFeature feature = featureModel.getFeature(featureNameList.get(i));
			oldColor.add(FeatureColorManager.getColor(feature));
			featureList.add(feature);
			FeatureColorManager.setColor(feature, newColor);
			implicitFeatures[i] = feature.getProperty().isImplicit();
			if (implicitFeatures[i]) {
				feature.getProperty().setImplicit(false);
				featureModel.fireEvent(new FeatureIDEEvent(feature, EventType.ATTRIBUTE_CHANGED));
			}
		}
		FeatureColorManager.notifyColorChange(featureList);
		return new FeatureIDEEvent(featureNameList, EventType.FEATURE_COLOR_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final ArrayList<IFeature> featureList = new ArrayList<>(featureNameList.size());
		for (int i = 0; i < featureNameList.size(); i++) {
			final IFeature feature = featureModel.getFeature(featureNameList.get(i));
			featureList.add(feature);
			FeatureColorManager.setColor(feature, oldColor.get(i));
			if (implicitFeatures[i]) {
				feature.getProperty().setImplicit(implicitFeatures[i]);
				featureModel.fireEvent(new FeatureIDEEvent(feature, EventType.ATTRIBUTE_CHANGED));
			}
		}
		FeatureColorManager.notifyColorChange(featureList);
		return new FeatureIDEEvent(featureNameList, EventType.FEATURE_COLOR_CHANGED);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_GRAPHICS;
	}

}
