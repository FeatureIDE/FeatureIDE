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
package de.ovgu.featureide.fm.core.conf.nodes;

import java.util.Collection;
import java.util.TreeSet;

public abstract class Expression extends Variable {

	protected final Variable[] children;
	
	public Expression(Variable[] children) {
		super(-1);
		this.children = children;
	}

	protected abstract byte computeValue();

	@Override
	public final byte getValue() {
		return (value == UNDEFINED) ? value = computeValue() : value;
	}

	@Override
	public final void setValue(byte value) {
	}
	
	@Override
	public final void reset() {
		value = UNDEFINED;
		for (int i = 0; i < children.length; i++) {
			children[i].reset();
		}
	}
	
	public byte updateValue() {
		reset();
		return value = computeValue();
	}
	
	public Collection<Integer> getVaraibles() {
		final TreeSet<Integer> idSet = new TreeSet<>();
		getVaraibles(idSet);
		return idSet;
		
	}
	
	protected void getVaraibles(TreeSet<Integer> list) {
		for (Variable variable : children) {
			variable.getVaraibles(list);
		}
	}

}
