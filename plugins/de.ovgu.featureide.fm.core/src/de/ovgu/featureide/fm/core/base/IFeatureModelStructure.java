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
package de.ovgu.featureide.fm.core.base;

import java.util.Collection;

/**
 * Manages all structural information of a feature model. Intended for tree structures (features are represented by tree nodes).
 *
 * @author Sebastian Krieter
 */
public interface IFeatureModelStructure {

	IFeatureModelStructure clone(IFeatureModel newFeatureNodel);

	IFeatureModel getFeatureModel();

	Collection<IFeature> getFeaturesPreorder();

	IFeatureStructure getRoot();

	boolean hasAbstract();

	boolean hasAlternativeGroup();

	boolean hasAndGroup();

	boolean hasConcrete();

	boolean hasHidden();

	boolean hasIndetHidden();

	boolean hasMandatoryFeatures();

	boolean hasOptionalFeatures();

	boolean hasOrGroup();

	int numAlternativeGroup();

	int numOrGroup();

	void replaceRoot(IFeatureStructure feature);

	void setRoot(IFeatureStructure root);

	boolean hasFalseOptionalFeatures();

	boolean hasUnsatisfiableConstraints();

	boolean hasTautologyConstraints();

	boolean hasDeadConstraints();

	boolean hasVoidModelConstraints();

	boolean hasRedundantConstraints();

	boolean hasDeadFeatures();

	void setShowHiddenFeatures(boolean showHiddenFeatures);

}
