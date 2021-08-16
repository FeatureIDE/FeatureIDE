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

import static de.ovgu.featureide.fm.core.localization.StringTable.CHANGE_GROUP_TYPE;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation with functionality to change group types. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class ChangeFeatureGroupTypeOperation extends AbstractFeatureModelOperation {

	public static final int ALTERNATIVE = 0;
	public static final int AND = 1;
	public static final int OR = 2;

	private final String featureName;
	private final int groupType;
	private int oldGroupType;

	public ChangeFeatureGroupTypeOperation(int groupType, String featureName, IFeatureModelManager featureModelManager) {
		super(featureModelManager, CHANGE_GROUP_TYPE);
		this.groupType = groupType;
		this.featureName = featureName;
	}

	/**
	 * Changes the structure group type of the feature named featureName depending on groupType, and stores the old group in oldGroupType. The returned event is
	 * an GROUP_TYPE_CHANGED event whose source is the feature named featureName.
	 */
	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(featureName);
		oldGroupType = getGroupType(feature);
		if (groupType == ALTERNATIVE) {
			feature.getStructure().changeToAlternative();
		} else if (groupType == OR) {
			feature.getStructure().changeToOr();
		} else {
			feature.getStructure().changeToAnd();
		}
		return new FeatureIDEEvent(feature, EventType.GROUP_TYPE_CHANGED, null, null);
	}

	/**
	 * Changes the structure group type back to oldGroupType.
	 */
	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(featureName);
		if (oldGroupType == ALTERNATIVE) {
			feature.getStructure().changeToAlternative();
		} else if (oldGroupType == AND) {
			feature.getStructure().changeToAnd();
		} else {
			feature.getStructure().changeToOr();
		}
		return new FeatureIDEEvent(feature, EventType.GROUP_TYPE_CHANGED, null, null);
	}

	/**
	 * Returns the group type of the given feature as saved in its structure.
	 *
	 * @param feature - {@link IFeature}
	 * @return int - either one of ALTERNATIVE, AND or OR.
	 */
	public static int getGroupType(IFeature feature) {
		if (feature.getStructure().isAlternative()) {
			return ALTERNATIVE;
		} else if (feature.getStructure().isAnd()) {
			return AND;
		} else {
			return OR;
		}
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
