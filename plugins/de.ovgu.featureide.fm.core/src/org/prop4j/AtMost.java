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
 * A constraint that is true iff at most a specified number of children is true.
 *
 * @author Thomas Thuem
 */
public class AtMost extends Node {

	public int max;

	public AtMost(int max, Object... children) {
		this.max = max;
		setChildren(children);
	}

	public AtMost(int max, Node[] children) {
		this.max = max;
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
		return new And(chooseKofN(newChildren, max + 1, true));
	}

	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		super.eliminate(list);
		if (!list.contains(getClass())) {
			return this;
		}

		final Node[] newNodes = chooseKofN(children, max + 1, true);
		return new And(newNodes);
	}

	@Override
	public Node clone() {
		return new AtMost(max, clone(children));
	}

	@Override
	public boolean getValue(Map<Object, Boolean> map) {
		int trueCount = 0;
		for (final Node child : children) {
			if (child.getValue(map)) {
				trueCount++;
				if (trueCount > max) {
					return false;
				}
			}
		}
		return true;
	}

}
