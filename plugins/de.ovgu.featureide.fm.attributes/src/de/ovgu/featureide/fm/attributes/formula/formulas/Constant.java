/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.attributes.formula.formulas;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.attributes.formula.AggregateFormula;

public class Constant implements AggregateFormula {

	double value;
	private final static String TYPE = "Constant";

	public Constant(double value) {
		this.value = value;
	}

	@Override
	public Double getResult(Map<String, Double> valueProviderMap) {
		return value;
	}

	@Override
	public Set<String> getVariables() {
		return new HashSet<String>();
	}

	@Override
	public String toString() {
		return String.valueOf(value);
	}

	@Override
	public String getUnit(Map<String, String> unitProviderMap) {
		return "";
	}

	@Override
	public String getType() {
		// TODO Auto-generated method stub
		return TYPE;
	}

}
