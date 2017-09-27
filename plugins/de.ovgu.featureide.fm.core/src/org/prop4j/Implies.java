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
package org.prop4j;

import java.util.List;
import java.util.Map;

/**
 * A constraint that is true iff the left child is false or the right child is true.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class Implies extends Node implements Cloneable {

	public Implies(Object leftChild, Object rightChild) {
		setChildren(leftChild, rightChild);
	}

	@Override
	public boolean isConjunctiveNormalForm() {
		return false;
	}

	@Override
	public boolean isClausalNormalForm() {
		return false;
	}

	@Override
	protected Node eliminateNonCNFOperators(Node[] newChildren) {
		return new Or(new Not(newChildren[0]), newChildren[1]);
	}

	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		super.eliminate(list);
		if (list.contains(getClass())) {
			return new Or(new Not(children[0]), children[1]);
		}
		return this;
	}

	@Override
	public int hashCode() {
		// TODO: This is equivalent not to implement hashCode() at all, and was added for legacy code reasons.
		// Please note: implementing "equals" without custom hashCode should be avoided
		return super.hashCode();
	}

	@Override
	public boolean equals(Object object) {
		if (!getClass().isInstance(object)) {
			return false;
		}
		final Implies implies = (Implies) object;
		return children[0].equals(implies.children[0]) && children[1].equals(implies.children[1]);
	}

	@Override
	public Node clone() {
		return new Implies(children[0].clone(), children[1].clone());
	}

	@Override
	public boolean getValue(Map<Object, Boolean> map) {
		return !children[0].getValue(map) || children[1].getValue(map);
	}

}
