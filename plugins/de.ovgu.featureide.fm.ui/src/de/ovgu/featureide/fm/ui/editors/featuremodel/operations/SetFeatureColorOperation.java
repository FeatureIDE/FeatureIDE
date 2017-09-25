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

import java.util.ArrayList;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;

/**
 * The operation to change the color of a feature. Enables redo and undo compatibility.
 *
 * @author Joshua Sprey
 */
public class SetFeatureColorOperation extends AbstractFeatureModelOperation {

	ArrayList<FeatureColor> oldColor;
	FeatureColor newColor;
	ArrayList<IFeature> features;

	/**
	 * @param featureModel
	 * @param label
	 */
	public SetFeatureColorOperation(IFeatureModel featureModel, ArrayList<IFeature> featureListBuffer, FeatureColor newColor) {
		super(featureModel, "Change feature color");
		features = featureListBuffer;
		this.newColor = newColor;
		oldColor = new ArrayList<>();
		for (int i = 0; i < featureListBuffer.size(); i++) {
			oldColor.add(FeatureColorManager.getColor(featureListBuffer.get(i)));
		}
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation#operation()
	 */
	@Override
	protected FeatureIDEEvent operation() {
		for (int i = 0; i < features.size(); i++) {
			final IFeature feature = features.get(i);
			FeatureColorManager.setColor(feature, newColor);
		}
		FeatureColorManager.notifyColorChange(features);
		return new FeatureIDEEvent(features, EventType.COLOR_CHANGED);
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation#inverseOperation()
	 */
	@Override
	protected FeatureIDEEvent inverseOperation() {
		for (int i = 0; i < features.size(); i++) {
			final IFeature feature = features.get(i);
			FeatureColorManager.setColor(feature, oldColor.get(i));
		}
		FeatureColorManager.notifyColorChange(features);
		return new FeatureIDEEvent(features, EventType.COLOR_CHANGED);
	}

}
