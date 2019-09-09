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

public class ProductFormula implements AggregateFormula {

	List<AggregateFormula> factors;
	List<Integer> potencies;
	private final static String TYPE = "Product";

	public ProductFormula(List<AggregateFormula> factors, List<Integer> potencies) {
		this.factors = factors;
		this.potencies = potencies;
	}

	@Override
	public Double getResult(Map<String, Double> valueProviderMap) {
		double result = 1;
		for (int i = 0; i < factors.size(); i++) {
			if (factors.get(i).getResult(valueProviderMap) == null) {
				return null;
			}
			result *= Math.pow(factors.get(i).getResult(valueProviderMap), potencies.get(i));
		}
		return result;
	}

	@Override
	public String toString() {
		String result = "";
		for (int i = 0; i < factors.size(); i++) {
			int sign = (potencies.get(i) == 1) ? FormulaStringTable.MULTIPLY : FormulaStringTable.DIVIDE;
			if (factors.get(i) instanceof AdditionFormula) {
				result += " " + (char) sign + " (" + factors.get(i).toString() + ")";
			} else {
				result += " " + (char) sign + " " + factors.get(i).toString();
			}

		}

		result = result.substring(3, result.length());
		return result;
	}

	@Override
	public Set<String> getVariables() {
		Set<String> variables = new HashSet<>();
		for (AggregateFormula factor : factors) {
			variables.addAll(factor.getVariables());
		}

		return variables;
	}

	@Override
	public String getUnit(Map<String, String> unitProviderMap) {
		String unit = "";
		for (int i = 0; i < factors.size(); i++) {
			String subUnit = factors.get(i).getUnit(unitProviderMap);
			if (subUnit == null) return null;
			if (subUnit.equals("")) continue;
			String operator = potencies.get(i) == 1 ? "*" : "/";
			unit += operator + subUnit;
		}
		if (unit.length() > 1) unit = unit.substring(1, unit.length());
		return unit;
	}

	@Override
	public String getType() {
		return TYPE;
	}

}
