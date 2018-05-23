/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.extended.ui.io.constraint;

public class WeightedTerm {

	private Integer weight;
	
	private boolean positive;
	
	private Reference reference;

	public WeightedTerm(Integer weight, boolean positive, Reference reference) {
		this.weight = weight;
		this.positive = positive;
		this.reference = reference;
	}

	public Integer getWeight() {
		return weight;
	}

	public boolean isPositive() {
		return positive;
	}

	public Reference getReference() {
		return reference;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(weight);
		sb.append(" ");
		if (!positive) 
			sb.append("~");
		sb.append(reference.toString());
		sb.append(")");
		return sb.toString();
	}
}
