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
package de.ovgu.featureide.fm.core.conf.nodes;

import java.util.Collection;
import java.util.TreeSet;

public abstract class Expression extends Variable {

	private static final long serialVersionUID = 3993773534104729866L;

	protected final Variable[] children;

	public Expression(Variable[] children) {
		super(-1);
		this.children = children;
	}

	protected abstract int computeValue();

	@Override
	public final int getValue() {
		return (value == UNDEFINED) ? value = computeValue() : value;
	}

	@Override
	public int getManualValue() {
		return getValue();
	}

	@Override
	public int getAutomaticValue() {
		return getValue();
	}

	@Override
	public final void setAutomaticValue(int value) {}

	@Override
	public final void setManualValue(int value) {}

	@Override
	public final void reset() {
		value = UNDEFINED;
		for (int i = 0; i < children.length; i++) {
			children[i].reset();
		}
	}

	public int updateValue() {
		reset();
		return value = computeValue();
	}

	public Collection<Integer> getVariables() {
		final TreeSet<Integer> idSet = new TreeSet<>();
		getVariables(idSet);
		return idSet;
	}

	@Override
	protected void getVariables(TreeSet<Integer> list) {
		for (final Variable variable : children) {
			variable.getVariables(list);
		}
	}

}
