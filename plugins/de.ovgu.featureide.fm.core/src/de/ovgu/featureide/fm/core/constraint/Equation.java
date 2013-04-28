/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.constraint;

import java.util.List;

/**
 * Connects a sum of {@link WeightedTerm}s to an integer with a certain {@link RelationOperator}.
 * 
 * @author Sebastian Henneberg
 */
public class Equation {

	private List<WeightedTerm> weightedTerms;
	
	private RelationOperator operator;
	
	private int degree;

	public Equation(List<WeightedTerm> weightedTerms, RelationOperator operator,
			int degree) {
		super();
		this.weightedTerms = weightedTerms;
		this.operator = operator;
		this.degree = degree;
	}

	public List<WeightedTerm> getWeightedTerms() {
		return weightedTerms;
	}

	public RelationOperator getOperator() {
		return operator;
	}

	public int getDegree() {
		return degree;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (WeightedTerm term : weightedTerms) {
			sb.append(term.toString() + " ");
		}
		sb.append(operator.toString() + " ");
		sb.append(degree);
		return sb.toString();
	}
}
