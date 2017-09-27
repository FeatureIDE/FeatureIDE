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

import java.util.Comparator;

import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Compares two literals based on their {@code var} object and {@code positive} state.
 *
 * @author Sebastian Krieter
 */
public class LiteralComparator implements Comparator<Literal> {

	@Override
	public int compare(Literal arg0, Literal arg1) {
		if (arg0.positive == arg1.positive) {
			if (arg0.var == arg1.var) {
				return 0;
			} else if ((arg0.var == NodeCreator.varTrue) || (arg0.var == NodeCreator.varFalse)) {
				return ((arg0.var == NodeCreator.varTrue) || (arg1.var != NodeCreator.varTrue)) ? -1 : 1;
			} else if ((arg1.var == NodeCreator.varTrue) || (arg1.var == NodeCreator.varFalse)) {
				return 1;
			} else {
				return ((String) arg0.var).compareTo((String) arg1.var);
			}
		} else if (arg0.positive) {
			return -1;
		} else {
			return 1;
		}
	}
}
