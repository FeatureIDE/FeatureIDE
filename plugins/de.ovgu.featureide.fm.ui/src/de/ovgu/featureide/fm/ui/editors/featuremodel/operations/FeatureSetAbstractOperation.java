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

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Operation with functionality to set a Feature abstract/concrete. Enables
 * undo/redo functionality.
 * 
 * @author Fabian Benduhn
 */
public class FeatureSetAbstractOperation extends AbstractFeatureModelOperation {

	private static final String LABEL_ABSTRACT = "Set Feature Abstract";
	private static final String LABEL_CONCRETE = "Set Feature Concrete";

	private Feature feature;

	/**
	 * @param label
	 *            Description of this operation to be used in the menu
	 * @param feature
	 *            feature on which this operation will be executed
	 * 
	 */
	public FeatureSetAbstractOperation(Feature feature, FeatureModel featureModel) {
		super(featureModel, getLabel(feature));
		this.feature = feature;
	}
	
	/**
	 * @param feature
	 * @return String to be used in undo/redo menu
	 */
	private static String getLabel(Feature feature) {
		if (feature.isAbstract())
			return LABEL_CONCRETE;
		else
			return LABEL_ABSTRACT;
	}

	@Override
	protected void redo() {
		feature.setAbstract(!feature.isAbstract());
	}

	@Override
	protected void undo() {
		redo();
	}
}
