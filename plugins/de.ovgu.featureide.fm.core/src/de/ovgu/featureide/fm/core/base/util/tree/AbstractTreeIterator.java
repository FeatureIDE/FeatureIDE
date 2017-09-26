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
package de.ovgu.featureide.fm.core.base.util.tree;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.NoSuchElementException;

/**
 * Abstract implementation of the {@link TreeIterator} interface.
 *
 * @author Sebastian Krieter
 */
public abstract class AbstractTreeIterator<M, E> implements TreeIterator<E> {

	protected LinkedList<ModelTree<M, E>> iteratorList = new LinkedList<>();

	protected ModelTree<M, E> next = null;

	protected AbstractTreeIterator(ModelTree<M, E> root) {
		iteratorList.add(root);
	}

	@Override
	public boolean hasNext() {
		return !iteratorList.isEmpty();
	}

	@Override
	public E next() {
		if (iteratorList.isEmpty()) {
			throw new NoSuchElementException();
		}
		next = getNext();
		return next.object;
	}

	protected abstract ModelTree<M, E> getNext();

	@Override
	public void remove() {
		if (next != null) {
			if (next.parent == null) {
				next.object = null;
			} else {
				final ListIterator<ModelTree<M, E>> listIterator = next.parent.children.listIterator();
				int i = 0;
				while (listIterator.hasNext()) {
					final ModelTree<M, E> n = listIterator.next();
					if (n == next) {
						listIterator.remove();
						break;
					}
					i++;
				}
				next.parent.children.addAll(i, next.children);
			}
			next = null;
		} else {
			throw new IllegalStateException();
		}
	}

	@Override
	public void removeSubtree() {
		if (next != null) {
			if (next.parent == null) {
				next.object = null;
				next.children.clear();
			} else {
				next.parent.children.remove(next);
			}
			next = null;
		} else {
			throw new IllegalStateException();
		}
	}

	@Override
	public Iterator<E> iterator() {
		return this;
	}

	@Override
	public int getCurrentLevel() {
		int level = -1;
		ModelTree<M, E> tempParent = next;
		while (tempParent != null) {
			tempParent = tempParent.getParent();
			level++;
		}
		return level;
	}

}
