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
 * A constraint that is true iff exactly a specified number of children is true.
 *
 * @author Thomas Thuem
 */
public class Choose extends Node {

	public int n;

	public Choose(int n, Object... children) {
		this.n = n;
		setChildren(children);
	}

	public Choose(int n, Node[] children) {
		this.n = n;
		setChildren(children);
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
		return new And(new AtMost(n, newChildren).eliminateNonCNFOperators(), new AtLeast(n, newChildren).eliminateNonCNFOperators());
	}

	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		super.eliminate(list);
		if (!list.contains(getClass())) {
			return this;
		}

		return new And(new AtMost(n, clone(children)), new AtLeast(n, clone(children)));
	}

	@Override
	public Node clone() {
		return new Choose(n, clone(children));
	}

	@Override
	public boolean getValue(Map<Object, Boolean> map) {
		int trueCount = 0;
		for (final Node child : children) {
			if (child.getValue(map)) {
				trueCount++;
				if (trueCount == n) {
					return true;
				}
			}
		}
		return false;
	}

}
