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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import static de.ovgu.featureide.fm.core.localization.StringTable.LOC_BY_EXTENSION;
import static de.ovgu.featureide.fm.core.localization.StringTable.LOC_BY_FEATURE;

import java.util.HashMap;

import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.HashMapNodeTwoStrings;

/**
 * Node for aggregated LOC.
 *
 * @author Schleicher Miro
 */
public class LOCNode extends LazyParent {

	private final HashMap<String, Integer> featureExtensionLOCList;

	LOCNode(String description, HashMap<String, Integer> fExList) {
		super(description);
		featureExtensionLOCList = fExList;
	}

	@Override
	protected void initChildren() {
		addChild(new HashMapNodeTwoStrings(LOC_BY_EXTENSION, 1, featureExtensionLOCList));
		addChild(new HashMapNodeTwoStrings(LOC_BY_FEATURE, 2, featureExtensionLOCList));

	}

}
