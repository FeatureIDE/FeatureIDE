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
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.attributes.formula.AggregateFormula;
import de.ovgu.featureide.fm.attributes.formula.FormulaStringTable;

public class AdditionFormula implements AggregateFormula {

	List<AggregateFormula> summands;
	List<Integer> signs;
	private final static String TYPE = "Addition";

	public AdditionFormula(List<AggregateFormula> summands, List<Integer> signs) {
		this.summands = summands;
		this.signs = signs;
		// TODO: CATCH #SIGNS != #SUMMANDS
	}

	@Override
	public Double getResult(Map<String, Double> valueProviderMap) {
		double result = 0;
		for (int i = 0; i < summands.size(); i++) {
			if (summands.get(i).getResult(valueProviderMap) == null) {
				return null;
			}
			result += summands.get(i).getResult(valueProviderMap) * signs.get(i);
		}

		return result;
	}

	@Override
	public String toString() {
		String result = "";
		for (int i = 0; i < summands.size(); i++) {
			int sign = (signs.get(i) == 1) ? FormulaStringTable.ADD : FormulaStringTable.SUBTRACT;
			result += " " + (char) sign + " " + summands.get(i).toString();
		}
		result = result.substring(3, result.length());
		return result;
	}

	@Override
	public Set<String> getVariables() {
		Set<String> variables = new HashSet<>();
		for (AggregateFormula summand : summands) {
			variables.addAll(summand.getVariables());
		}

		return variables;
	}

	@Override
	public String getUnit(Map<String, String> unitProviderMap) {
		String unit = summands.get(0).getUnit(unitProviderMap);
		for (int i = 0; i < summands.size(); i++) {
			if (summands.get(i).getUnit(unitProviderMap) == null || !unit.equals(summands.get(i).getUnit(unitProviderMap))) {
				return null;
			}
		}
		return unit;
	}

	@Override
	public String getType() {
		return TYPE;
	}

}
