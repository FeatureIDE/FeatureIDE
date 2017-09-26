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
package de.ovgu.featureide.fm.ui.views.outline.standard;

import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * Holds information for the GroupStates of features in outline views
 *
 * @author Jan Wedding
 * @author Marcus Pinnecke
 */
public class FmOutlineGroupStateStorage {

	private final IFeature feature;
	private final boolean isOrGroup;

	public FmOutlineGroupStateStorage(IFeature parentFeature, boolean isOr) {
		feature = parentFeature;
		isOrGroup = isOr;
	}

	public boolean isOrGroup() {
		return isOrGroup;
	}

	public IFeature getFeature() {
		return feature;
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + ((feature == null) ? 0 : feature.hashCode());
		return (prime * result) + (isOrGroup ? 1231 : 1237);
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final FmOutlineGroupStateStorage other = (FmOutlineGroupStateStorage) obj;
		if (feature == null) {
			if (other.feature != null) {
				return false;
			}
		} else if (!feature.equals(other.feature)) {
			return false;
		}
		if (isOrGroup != other.isOrGroup) {
			return false;
		}
		return true;
	}

}
