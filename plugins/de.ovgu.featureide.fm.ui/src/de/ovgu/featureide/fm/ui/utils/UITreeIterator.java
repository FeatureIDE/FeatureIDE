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
package de.ovgu.featureide.fm.ui.utils;

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;

/**
 * Traverses a {@link Tree} in preorder.
 *
 * @author Sebastian Krieter
 */
public class UITreeIterator implements Iterator<TreeItem> {

	private final LinkedList<TreeItem> itemQueue = new LinkedList<>();

	public UITreeIterator(Tree tree) {
		itemQueue.addAll(Arrays.asList(tree.getItems()));
	}

	@Override
	public boolean hasNext() {
		return !itemQueue.isEmpty();
	}

	@Override
	public TreeItem next() {
		final TreeItem next = itemQueue.removeFirst();
		itemQueue.addAll(0, Arrays.asList(next.getItems()));
		return next;
	}

	@Override
	public void remove() {
		throw new UnsupportedOperationException();
	}

}
