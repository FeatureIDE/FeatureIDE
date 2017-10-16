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

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.FeatureComparator;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;

/**
 * Parent node which evaluates if it has children before actually displaying them. All features are sorted in an alphabetical order ignoring the case.
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public final class FeatureListNode extends LazyParent {

	private final Collection<IFeature> list;

	private final boolean expand;

	public FeatureListNode(String description, Collection<IFeature> collection) {
		this(description, collection, collection.size(), true);
	}

	public FeatureListNode(String description, Collection<IFeature> collection, Object value, boolean expand) {
		super(description, value);

		this.expand = expand;

		final List<IFeature> list = new LinkedList<IFeature>(collection);
		Collections.sort(list, new FeatureComparator(false));

		this.list = list;
		lazy = (list.size() != 0);
	}

	@Override
	protected void initChildren() {
		for (final IFeature feat : list) {
			addChild(new FeatureNode(feat, expand));
		}
	}
}
