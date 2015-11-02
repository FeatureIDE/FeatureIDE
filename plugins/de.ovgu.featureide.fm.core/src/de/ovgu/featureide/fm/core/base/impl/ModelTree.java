/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.NoSuchElementException;

import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * Tree element.
 * 
 * @author Sebastian Krieter
 * 
 */
public class ModelTree<M, E> implements Iterable<E> {

	public static interface TreeIterator<E> extends Iterator<E>, Iterable<E> {
		void removeSubtree();
	}

	private static abstract class AbstractTreeIterator<M, E> implements TreeIterator<E> {

		protected LinkedList<ModelTree<M, E>> iteratorList = new LinkedList<>();

		protected ModelTree<M, E> next = null;

		private AbstractTreeIterator(ModelTree<M, E> root) {
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
					ListIterator<ModelTree<M, E>> listIterator = next.parent.children.listIterator();
					int i = 0;
					while (listIterator.hasNext()) {
						ModelTree<M, E> n = listIterator.next();
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

	}

	private static final class PreOrderIterator<M, E> extends AbstractTreeIterator<M, E> {

		private PreOrderIterator(ModelTree<M, E> root) {
			super(root);
		}

		public ModelTree<M, E> getNext() {
			final ModelTree<M, E> next = iteratorList.removeFirst();
			iteratorList.addAll(0, next.children);
			return next;
		}

	}

	private static final class LevelOrderIterator<M, E> extends AbstractTreeIterator<M, E> {

		private LevelOrderIterator(ModelTree<M, E> root) {
			super(root);
		}

		public ModelTree<M, E> getNext() {
			final ModelTree<M, E> next = iteratorList.removeFirst();
			iteratorList.addAll(0, next.children);
			return next;
		}

	}

	private static final class Converter<M, E> implements Functional.IFunction<ModelTree<M, E>, E> {
		@Override
		public E invoke(ModelTree<M, E> tree) {
			return tree.object;
		}
	}

	protected final M treeModel;

	protected final List<ModelTree<M, E>> children = new ArrayList<>();

	protected E object;

	protected ModelTree<M, E> parent = null;

	public ModelTree(E object) {
		this(object, null);
	}

	public ModelTree(E object, M treeModel) {
		this.object = object;
		this.treeModel = treeModel;
	}

	public List<ModelTree<M, E>> getChildren() {
		return Collections.unmodifiableList(children);
	}

	public Iterable<E> getChildrenObjects() {
		return Functional.map(children, new Converter<M, E>());
	}

	public ModelTree<M, E> getParent() {
		return parent;
	}

	public E getParentObject() {
		if (parent == null) {
			return null;
		}
		return parent.object;
	}

	public TreeIterator<E> iterator() {
		return new PreOrderIterator<M, E>(this);
	}

	public TreeIterator<E> preOrderIterator() {
		return new PreOrderIterator<M, E>(this);
	}

	public TreeIterator<E> levelOrderIterator() {
		return new LevelOrderIterator<M, E>(this);
	}

	public void addNode(E newChildObject) {
		ModelTree<M, E> newChild = new ModelTree<>(newChildObject, this.treeModel);
		newChild.parent = this;
		children.add(newChild);
	}

	public void addSubTree(ModelTree<M, E> newChild) {
		newChild.parent = this;
		children.add(newChild);
	}

	public void removeSubTree(ModelTree<M, E> child) {
		for (TreeIterator<E> it = iterator(); it.hasNext();) {
			if (it.next().equals(child)) {
				it.removeSubtree();
				break;
			}
		}
	}

	public void removeNode(E child) {
		for (TreeIterator<E> it = iterator(); it.hasNext();) {
			if (it.next().equals(child)) {
				it.remove();
				break;
			}
		}
	}

	public E getObject() {
		return object;
	}

	public M getModel() {
		return treeModel;
	}

	public boolean hasChildren() {
		return !children.isEmpty();
	}

	public int getNumberOfChildren() {
		return children.size();
	}

	public boolean isRoot() {
		return parent == null;
	}
	
	public void reverse() {
		for (ModelTree<M, E> child : children) {
			child.reverse();
		}
		Collections.reverse(children);
	}
	
	public boolean isAncestorOf(ModelTree<?, ?> tree) {
		if (this == tree) {
			return true;
		}
		ModelTree<M, E> curParent = parent;
		while (curParent != null) {
			if (tree == curParent) {
				return true;
			}
			curParent = curParent.parent;
		}
		return false;
	}

}
