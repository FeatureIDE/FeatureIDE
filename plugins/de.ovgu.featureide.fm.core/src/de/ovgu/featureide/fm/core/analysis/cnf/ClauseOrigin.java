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
package de.ovgu.featureide.fm.core.analysis.cnf;

import de.ovgu.featureide.fm.core.base.IFeatureModelElement;

/**
 * Stores information about a {@link LiteralSet clause}.
 *
 * @author Sebastian Krieter
 */
public class ClauseOrigin {

	public static enum OriginType {
		ParentChild, Mandatory, Or, Alternative, Root, Constraint, Derived
	}

	private final OriginType originType;

	/**
	 * IConstraint or IFeature (always the parent element),
	 */
	private final IFeatureModelElement originObject;

	public ClauseOrigin(OriginType originType, IFeatureModelElement originObject) {
		this.originType = originType;
		this.originObject = originObject;
	}

	public OriginType getOriginType() {
		return originType;
	}

	public IFeatureModelElement getOriginObject() {
		return originObject;
	}

}
