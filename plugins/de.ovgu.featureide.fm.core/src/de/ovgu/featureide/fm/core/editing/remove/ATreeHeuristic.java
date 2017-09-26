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
package de.ovgu.featureide.fm.core.editing.remove;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Abstract extension of {@link AFeatureOrderHeuristic} for heuristic that work on a feature tree.
 *
 * @author Sebastian Krieter
 */
public abstract class ATreeHeuristic extends AFeatureOrderHeuristic {

	protected final int[] indexArray;
	protected int indexArrayIndex = 0;

	public ATreeHeuristic(DeprecatedFeature[] map, int length, IFeatureModel featureModel) {
		super(map, length);
		indexArray = new int[length];
		order(featureModel.getStructure().getRoot());
	}

	@Override
	protected int getNextIndex() {
		return indexArray[curIndex];
	}

	protected abstract void order(IFeatureStructure root);

	protected void nextIndex() {
		indexArrayIndex++;
	}

	protected final void find(IFeature feature) {
		for (int i = 0; i < map.length; i++) {
			final DeprecatedFeature deprecatedFeature = map[i];
			if ((deprecatedFeature != null) && deprecatedFeature.getFeature().equals(feature.getName())) {
				indexArray[indexArrayIndex] = i;
				nextIndex();
				break;
			}
		}
	}

}
