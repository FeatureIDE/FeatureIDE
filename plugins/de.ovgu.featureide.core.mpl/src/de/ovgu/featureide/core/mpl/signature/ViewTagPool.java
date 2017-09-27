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
package de.ovgu.featureide.core.mpl.signature;

import java.util.HashMap;
import java.util.NavigableSet;
import java.util.TreeSet;

/**
 * Contains the instances of different {@link ViewTag}s.
 *
 * @author Sebastian Krieter
 */
public class ViewTagPool {

	private final HashMap<ViewTag, ViewTag> map = new HashMap<ViewTag, ViewTag>();
	private final TreeSet<ViewTag> set = new TreeSet<ViewTag>();

	public ViewTag getViewTag(String name, int level) {
		return getViewTag(new ViewTag(name, level));
	}

	public ViewTag getViewTag(String name) {
		return getViewTag(new ViewTag(name));
	}

	private synchronized ViewTag getViewTag(ViewTag newVT) {
		final ViewTag existingVT = map.get(newVT);
		if (existingVT == null) {
			set.add(newVT);
			map.put(newVT, newVT);
			return newVT;
		} else {
			return existingVT;
		}
	}

	public synchronized void removeViewTag(String name) {
		final ViewTag startVt = new ViewTag(name, 0), endVt = new ViewTag(name);

		final NavigableSet<ViewTag> subSet = set.subSet(startVt, true, endVt, true);
		for (final ViewTag viewTag : subSet) {
			map.remove(viewTag);
		}
		subSet.clear();
	}

	public synchronized void scaleUpViewTags(String name, int minimumLevel) {
		final ViewTag startVt = new ViewTag(name, minimumLevel), endVt = new ViewTag(name);

		for (final ViewTag curVt : set.subSet(startVt, true, endVt, true)) {
			curVt.scaleUp();
		}
	}
}
