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

public class And2 extends Expression {

	private static final long serialVersionUID = 8373469012995551048L;

	public And2(Variable[] children) {
		super(children);
	}

	@Override
	protected int computeValue() {
		byte ret = TRUE;
		for (int i = 0; i < children.length; i++) {
			final int childValue = children[i].getValue();
			switch (childValue) {
			case FALSE:
				return FALSE;
			case UNDEFINED:
				ret = UNDEFINED;
			default:
				continue;
			}
		}
		return ret;
	}

}
