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

/**
 * Manages all additional properties of a feature.
 *
 * @author Sebastian Krieter
 */
public interface IFeatureProperty {

	IFeatureProperty clone(IFeature newFeature);

	String getDescription();

	@Deprecated
	String getDisplayName();

	IFeature getFeature();

	void setDescription(CharSequence description);

	@Deprecated
	void setDisplayName(CharSequence name);

	boolean isConstraintSelected();

	boolean selectConstraint(boolean state);

	/**
	 * Implicit features can be used to represent features that exist only for technical reasons, such as the implicit root feature of UVL models with multiple
	 * actual root features.
	 *
	 * @return Whether the corresponding feature is implicit.
	 */
	boolean isImplicit();

	void setImplicit(boolean implicit);
}
