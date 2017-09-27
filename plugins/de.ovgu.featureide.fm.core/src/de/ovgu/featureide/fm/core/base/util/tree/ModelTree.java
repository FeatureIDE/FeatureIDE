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

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * Tree element.
 *
 * TODO remove this class as it seems to be redundant to the feature structure and needs to be updated all the time.S
 *
 * @author Sebastian Krieter
 *
 */
public class ModelTree<M, E> implements Iterable<E> {

	private static final class PreOrderIterator<M, E> extends AbstractTreeIterator<M, E> {

		private PreOrderIterator(ModelTree<M, E> root) {
			super(root);
		}

		@Override
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

		@Override
		public ModelTree<M, E> getNext() {
			final ModelTree<M, E> next = iteratorList.removeFirst();
			iteratorList.addAll(next.children);
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

	@Override
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
		final ModelTree<M, E> newChild = new ModelTree<>(newChildObject, this.treeModel);
		newChild.parent = this;
		children.add(newChild);
	}

	public void addNodeAtIndex(E newChildObject, int index) {
		final ModelTree<M, E> newChild = new ModelTree<>(newChildObject, this.treeModel);
		newChild.parent = this;
		children.add(index, newChild);
	}

	public void addSubTree(ModelTree<M, E> newChild) {
		newChild.parent = this;
		children.add(newChild);
	}

	public void addSubTreeAtIndex(int index, ModelTree<M, E> newChild) {
		newChild.parent = this;
		children.add(index, newChild);
	}

	public void removeSubTree(ModelTree<M, E> child) {
		for (final Iterator<ModelTree<M, E>> it = children.iterator(); it.hasNext();) {
			final ModelTree<M, E> next = it.next();
			if (next.equals(child)) {
				it.remove();
				return;
			}
		}
	}

	public void removeNode(E child) {
		for (final TreeIterator<E> it = iterator(); it.hasNext();) {
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

	public int getNumberOfNodes() {
		int count = 0;
		final LinkedList<ModelTree<M, E>> countList = new LinkedList<>();
		countList.add(this);
		do {
			final ModelTree<M, E> next = countList.removeFirst();
			countList.addAll(0, next.children);
			count++;
		} while (!countList.isEmpty());
		return count;
	}

	public boolean isRoot() {
		return parent == null;
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

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (final TreeIterator<E> it = this.iterator(); it.hasNext();) {
			final E element = it.next();
			for (int i = 0; i < it.getCurrentLevel(); i++) {
				sb.append('\t');
			}
			sb.append(element.toString());
			sb.append('\n');
		}
		return sb.toString();
	}

}
