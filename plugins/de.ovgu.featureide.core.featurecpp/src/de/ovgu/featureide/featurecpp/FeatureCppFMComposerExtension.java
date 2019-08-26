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
package de.ovgu.featureide.featurecpp;

import de.ovgu.featureide.fm.core.FMComposerExtension;

public class FeatureCppFMComposerExtension extends FMComposerExtension {

	/**
	 * Matches valid c identifier First character is a letter or underscore Others are letters, numbers, underscore
	 */
	public static final String FEATURE_NAME_PATTERN = "^[a-zA-Z_]\\w*$";

	@Override
	protected boolean isValidFeatureNameComposerSpecific(String s) {
		return s.matches(FEATURE_NAME_PATTERN);
	}

}
