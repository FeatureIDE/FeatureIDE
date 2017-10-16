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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;

/**
 *
 * @author Sebastian Krieter
 */
public class Condition implements Comparable<Condition> {

	private final LiteralSet[] positiveExpressions, negativeExpressions;

	private int outgoingEdge = 0;

	public Condition(LiteralSet[] positiveExpressions, LiteralSet[] negativeExpressions) {
		super();
		this.positiveExpressions = positiveExpressions;
		this.negativeExpressions = negativeExpressions;
	}

	public LiteralSet[] getPositiveExpressions() {
		return positiveExpressions;
	}

	public LiteralSet[] getNegativeExpressions() {
		return negativeExpressions;
	}

	public int getOutgoingEdge() {
		return outgoingEdge;
	}

	public void setOutgoingEdge(int outgoingEdge) {
		this.outgoingEdge = outgoingEdge;
	}

	@Override
	public int compareTo(Condition o) {
		return outgoingEdge - o.outgoingEdge;
	}

}
