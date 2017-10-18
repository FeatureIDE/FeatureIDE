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
package de.ovgu.featureide.fm.core;

import java.io.Serializable;
import java.util.Comparator;

import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * Compares two {@link IFeature}s by their name.
 *
 * @author Sebastian Krieter
 */
public class FeatureComparator implements Comparator<IFeature>, Serializable {

	private static final long serialVersionUID = 3133122730880756050L;

	private final boolean caseSensitive;

	public FeatureComparator(boolean caseSensitive) {
		this.caseSensitive = caseSensitive;
	}

	@Override
	public int compare(IFeature feature1, IFeature feature2) {
		return caseSensitive ? feature1.getName().compareTo(feature2.getName()) : feature1.getName().compareToIgnoreCase(feature2.getName());
	}

}
