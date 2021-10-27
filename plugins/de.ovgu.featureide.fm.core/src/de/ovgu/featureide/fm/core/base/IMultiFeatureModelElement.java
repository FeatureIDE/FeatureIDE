/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
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

import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;

/**
 * The {@link IMultiFeatureModelElement} interface allows features and constraints of a {@link MultiFeatureModel} to have different types regarding where they
 * are coming from.
 *
 * @author Benedikt Jutz
 */
public interface IMultiFeatureModelElement {

	public static final int TYPE_INTERN = 0;
	public static final int TYPE_INHERITED = 1;
	public static final int TYPE_INTERFACE = 2;
	public static final int TYPE_INSTANCE = 3;

	/**
	 * Sets the type of this element, which lies between 0 and 3.
	 *
	 * @param type - int
	 */
	void setType(int type);

	/**
	 * Returns the current type of this element.
	 *
	 * @return int
	 */
	int getType();

	default boolean isFromExtern() {
		return getType() != TYPE_INTERN;
	}

	default boolean isInherited() {
		return getType() == TYPE_INHERITED;
	}

	default boolean isInterface() {
		return getType() == TYPE_INTERFACE;
	}

	default boolean isInstance() {
		return getType() == TYPE_INSTANCE;
	}
}
