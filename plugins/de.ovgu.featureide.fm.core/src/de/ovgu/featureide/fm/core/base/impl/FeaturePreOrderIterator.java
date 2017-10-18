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
package de.ovgu.featureide.fm.core.base.impl;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.NoSuchElementException;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Returns all features of a feature model in pre-order.
 *
 * @author Sebastian Krieter
 */
public class FeaturePreOrderIterator implements Iterator<IFeature> {

	private final LinkedList<IFeatureStructure> featureStructureList = new LinkedList<>();

	public FeaturePreOrderIterator(IFeatureModel featureModel) {
		final IFeatureStructure root = featureModel.getStructure().getRoot();
		if (root != null) {
			featureStructureList.add(root);
		}
	}

	@Override
	public boolean hasNext() {
		return !featureStructureList.isEmpty();
	}

	@Override
	public IFeature next() {
		if (!hasNext()) {
			throw new NoSuchElementException();
		}
		final IFeatureStructure removeFirst = featureStructureList.removeFirst();
		if (removeFirst.hasChildren()) {
			featureStructureList.addAll(0, removeFirst.getChildren());
		}
		return removeFirst.getFeature();
	}

	@Override
	public void remove() {
		throw new UnsupportedOperationException();
	}

}
