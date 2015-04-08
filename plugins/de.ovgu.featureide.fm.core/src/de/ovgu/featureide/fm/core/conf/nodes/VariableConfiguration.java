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

import java.util.Iterator;


public class VariableConfiguration implements Iterable<Variable> {
	
	private final Variable[] conf;

	public VariableConfiguration(int count) {
		conf = new Variable[count];
		for (int i = 0; i < conf.length; i++) {
			conf[i] = new Variable(i);
		}
	}
	
	public void setVariable(int index, byte newValue) {
		conf[index].setValue(newValue);
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
			public void remove() {
			}
		};
	}
}
