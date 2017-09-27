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

import java.util.LinkedList;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Implementation of {@link AFeatureOrderHeuristic}. Returns features in reverse-level-order according to the feature tree.
 *
 * @author Sebastian Krieter
 */
public class ReverseLevelOrderHeuristic extends ATreeHeuristic {

	public ReverseLevelOrderHeuristic(DeprecatedFeature[] map, int length, IFeatureModel featureModel) {
		super(map, length, featureModel);
	}

	@Override
	protected void order(IFeatureStructure root) {
		indexArrayIndex = indexArray.length - 1;
		final LinkedList<IFeatureStructure> list = new LinkedList<>();
		list.add(root);
		while (!list.isEmpty()) {
			final IFeatureStructure nextFeature = list.removeFirst();
			list.addAll(nextFeature.getChildren());
			find(nextFeature.getFeature());
		}
	}

	@Override
	protected void nextIndex() {
		indexArrayIndex--;
	}

}
