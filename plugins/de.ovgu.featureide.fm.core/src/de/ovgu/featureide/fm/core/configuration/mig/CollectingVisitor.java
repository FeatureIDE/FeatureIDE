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
package de.ovgu.featureide.fm.core.configuration.mig;

import org.sat4j.core.VecInt;

public class CollectingVisitor implements Visitor<VecInt[]> {
	final VecInt[] literalList = new VecInt[] { new VecInt(), new VecInt() };

	@Override
	public void visitStrong(int curLiteral) {
		literalList[0].push(curLiteral);
	}

	@Override
	public void visitWeak(int curLiteral) {
		literalList[1].push(curLiteral);
	}

	@Override
	public VecInt[] getResult() {
		return literalList;
	}
}
