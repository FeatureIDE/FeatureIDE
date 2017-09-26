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

import java.io.Serializable;
import java.util.TreeSet;

public class Variable implements Serializable {

	private static final long serialVersionUID = 2253729345725413110L;

	public static final int TRUE = 2, FALSE = 1, UNDEFINED = 0;

	protected final int id;

	protected int value;

	public Variable(int id) {
		this(id, UNDEFINED);
	}

	public Variable(int id, int value) {
		this.id = id;
		setManualValue(value);
	}

	public int getId() {
		return id;
	}

	public boolean hasValue() {
		return value > UNDEFINED;
	}

	public int getValue() {
		return getManualValue() | getAutomaticValue();
	}

	public int getManualValue() {
		return value & 3;
	}

	public int getAutomaticValue() {
		return value >> 2;
	}

	void setManualValue(int value) {
		this.value = (this.value & 0xfffffffc) | value;
		assert (getValue() <= TRUE) && (getValue() >= UNDEFINED) : "Invalid Variable Configuration";
	}

	void setAutomaticValue(int value) {
		this.value = (this.value & 0xfffffff3) | (value << 2);
		assert (getValue() <= TRUE) && (getValue() >= UNDEFINED) : "Invalid Variable Configuration";
	}

	protected void reset() {}

	protected void getVariables(TreeSet<Integer> list) {
		list.add(id);
	}

	@Override
	public String toString() {
		switch (getValue()) {
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
