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
 * Operation with functionality to change group types. Enables undo/redo
 * functionality.
 * 
 * @author Fabian Benduhn
 */
public class FeatureChangeGroupTypeOperation extends AbstractFeatureModelOperation {

	private static final String LABEL = "Change Group Type";
	public static final int ALTERNATIVE = 0;
	public static final int AND = 1;
	public static final int OR = 2;

	protected Feature feature;
	private int groupType;
	private int oldGroupType;

	/**
	 * Grouptype of feature will be set to groupType when this operation is
	 * executed
	 */
	public FeatureChangeGroupTypeOperation(int groupType, Feature feature,
			FeatureModel featureModel) {
		super(featureModel, LABEL);
		this.groupType = groupType;
		this.oldGroupType = getGroupType(feature);
		this.feature = feature;
	}

	@Override
	protected void redo() {
		if (groupType == ALTERNATIVE) {
			feature.changeToAlternative();
		} else if (groupType == OR) {
			feature.changeToOr();
		} else {
			feature.changeToAnd();
		}
	}

	@Override
	protected void undo() {
		if (oldGroupType == ALTERNATIVE) {
			feature.changeToAlternative();
		} else if (oldGroupType == AND) {
			feature.changeToAnd();
		} else {
			feature.changeToOr();
		}
	}

	private static int getGroupType(Feature feature) {
		if (feature.isAlternative()) {
			return ALTERNATIVE;
		} else if (feature.isAnd()) {
			return AND;
		} else {
			return OR;
		}
	}

}
