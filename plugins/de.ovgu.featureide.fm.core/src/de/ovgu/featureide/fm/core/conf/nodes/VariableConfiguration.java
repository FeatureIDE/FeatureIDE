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

import java.util.Iterator;

public class VariableConfiguration implements Iterable<Variable> {

	private final Variable[] conf;
	private int valueCount = 0;

	public VariableConfiguration(int count) {
		conf = new Variable[count];
		for (int i = 0; i < conf.length; i++) {
			conf[i] = new Variable(i);
		}
	}

	public void setVariable(int index, int newValue, boolean manual) {
		final Variable variable = conf[index];
		final boolean hasValue = variable.hasValue();
		if (manual) {
			variable.setManualValue(newValue);
		} else {
			variable.setAutomaticValue(newValue);
		}
		if (hasValue != variable.hasValue()) {
			valueCount += hasValue ? -1 : 1;
		}
	}

	public int size() {
		return size(false);
	}

	public int size(boolean definedVariablesOnly) {
		return definedVariablesOnly ? valueCount : conf.length;
	}

	public Variable getVariable(int index) {
		return conf[index];
	}

	@Override
	public Iterator<Variable> iterator() {
		return new Iterator<Variable>() {

			private int index = 0;

			@Override
			public boolean hasNext() {
				return index < conf.length;
			}

			@Override
			public Variable next() {
				return conf[index++];
			}

			@Override
			public void remove() {}
		};
	}

	@Override
	public String toString() {
		final StringBuffer sb = new StringBuffer();
		for (int i = 0; i < conf.length; i++) {
			sb.append(conf[i]);
			sb.append('\n');
		}
		return sb.toString();
	}

	public void reset() {
		for (int i = 0; i < conf.length; i++) {
			final Variable variable = conf[i];
			variable.setManualValue(Variable.UNDEFINED);
			variable.setAutomaticValue(Variable.UNDEFINED);
		}
	}

}
