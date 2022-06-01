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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.preferences;

/**
 * Stores the preference value for omitting the dummy root when saving a feature model in DIMACS format.
 *
 * @author Sebastian Krieter
 */
public class DIMACSOmitRootPreference extends BooleanPreference {

	private static final DIMACSOmitRootPreference INSTANCE = new DIMACSOmitRootPreference();

	public static final DIMACSOmitRootPreference getInstance() {
		return INSTANCE;
	}

	private DIMACSOmitRootPreference() {
		super("DIMACSOmitRoot");
	}

	@Override
	public Boolean getDefault() {
		return Boolean.TRUE;
	};

}
