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
package de.ovgu.featureide.fm.core.base;

import org.prop4j.Node;

/**
 * Factory to create or copy instances of {@link IFeature}, {@link IFeatureModel}, {@link IConstraint}, and to obfuscate {@link IFeatureModel}s.
 *
 * @author Sebastian Krieter
 * @author Rahel Arens
 * @author Benedikt Jutz
 */
public interface IFeatureModelFactory extends IFactory<IFeatureModel> {

	public static String extensionPointID = "FMFactory";

	public static String extensionID = "fmFactory";

	IConstraint createConstraint(IFeatureModel featureModel, Node propNode);

	IFeature createFeature(IFeatureModel featureModel, String name);

	IFeatureModel createObfuscatedFeatureModel(IFeatureModel featureModel, String salt);

	/**
	 * Creates a copy of a feature with the feature type of the factory.
	 *
	 * @param featureModel The feature model of the new feature
	 * @param oldFeature The feature to be copied
	 * @param copyId If <code>true</code> the id of the old feature is kept. Otherwise a new id is assigned to the new feature.
	 * @return A copy of the feature <code>oldFeature</code>, with the feature type of the factory.
	 */
	IFeature copyFeature(IFeatureModel featureModel, IFeature oldFeature, boolean copyId);

	/**
	 * Default implementation of {@link IFeatureModelFactory#copyFeature(IFeatureModel, IFeature, boolean)} where <code>copyId</code> is <code>true</code>.
	 *
	 * @param featureModel The feature model of the new feature
	 * @param oldFeature The feature to be copied
	 * @return A copy of the feature <code>oldFeature</code>, with the feature type of the factory.
	 */
	default IFeature copyFeature(IFeatureModel featureModel, IFeature oldFeature) {
		return copyFeature(featureModel, oldFeature, true);
	}

	/**
	 * Creates a copy of a constraint with the constraint type of the factory.
	 *
	 * @param featureModel The feature model of the new constraint
	 * @param oldConstraint The constraint to be copied
	 * @param copyId If <code>true</code> the id of the old constraint is kept. Otherwise a new id is assigned to the new constraint.
	 * @return A copy of the constraint <code>oldConstraint</code>, with the constraint type of the factory.
	 */
	IConstraint copyConstraint(IFeatureModel featureModel, IConstraint oldConstraint, boolean copyId);

	/**
	 * Default implementation of {@link IFeatureModelFactory#copyConstraint(IFeatureModel, IConstraint, boolean)} where <code>copyId</code> is
	 * <code>true</code>.
	 *
	 * @param featureModel The feature model of the new constraint
	 * @param oldConstraint The constraint to be copied
	 * @return A copy of the constraint <code>oldConstraint</code>, with the constraint type of the factory.
	 */
	default IConstraint copyConstraint(IFeatureModel featureModel, IConstraint oldConstraint) {
		return copyConstraint(featureModel, oldConstraint, true);
	}
}
