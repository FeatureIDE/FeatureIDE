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

import java.io.Serializable;
import java.util.TreeSet;

public class Variable implements Serializable {

	private static final long serialVersionUID = 2253729345725413110L;

	public static final byte TRUE = 1, FALSE = 0, UNDEFINED = -1;

	protected final int id;

	protected byte value;

	public Variable(int id) {
		this(id, UNDEFINED);
	}

	public Variable(int id, byte value) {
		this.id = id;
		this.value = value;
	}

	public byte getValue() {
		return value;
	}

	public int getId() {
		return id;
	}

	public void setValue(byte value) {
		this.value = value;
	}

	protected void reset() {
	}

	protected void getVaraibles(TreeSet<Integer> list) {
		list.add(id);
	}

	@Override
	public String toString() {
		switch (value) {
		case TRUE:
			return id + " : true";
		case FALSE:
			return id + " : false";
		case UNDEFINED:
			return id + " : undefined";
		default:
			return "! " + id + " : invalid value!";
		}
	}

}
