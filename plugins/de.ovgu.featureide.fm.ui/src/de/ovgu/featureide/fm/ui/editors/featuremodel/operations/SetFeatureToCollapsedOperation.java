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

import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURE_COLLAPSED;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURE_EXPANDED;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;

/**
 * TODO description
 * 
 * @author Joshua Sprey
 * @author Enis Belli
 */
public class SetFeatureToCollapsedOperation extends AbstractFeatureModelOperation {

	private IFeature feature;

	/**
	 * @param label
	 *            Description of this operation to be used in the menu
	 * @param feature
	 *            feature on which this operation will be executed
	 * 
	 */
	public SetFeatureToCollapsedOperation(IFeature feature, IFeatureModel featureModel) {
		super(featureModel, getLabel(feature));
		this.feature = feature;
	}

	/**
	 * @param feature
	 * @return String to be used in undo/redo menu
	 */
	private static String getLabel(IFeature feature) {
		if (feature.getStructure().isCollapsed())
			return SET_FEATURE_COLLAPSED;
		else
			return SET_FEATURE_EXPANDED;
	}

	@Override
	protected FeatureIDEEvent operation() {
		feature.getStructure().setCollapsed(!feature.getStructure().isCollapsed());
		return new FeatureIDEEvent(feature, EventType.COLLAPSED_CHANGED, Boolean.FALSE, Boolean.TRUE);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		return operation();
	}

}
