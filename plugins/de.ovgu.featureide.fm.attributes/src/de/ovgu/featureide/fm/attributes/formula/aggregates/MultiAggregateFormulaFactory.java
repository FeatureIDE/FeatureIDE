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
package de.ovgu.featureide.fm.attributes.formula.aggregates;

import java.util.HashMap;
import java.util.Map;

import de.ovgu.featureide.fm.attributes.formula.AggregateFormula;
import de.ovgu.featureide.fm.attributes.formula.FormulaStringTable;
import de.ovgu.featureide.fm.attributes.formula.provider.FormulaValueProvider;

public class MultiAggregateFormulaFactory {

	String[] formulaTypes = { FormulaStringTable.SUM, FormulaStringTable.MAX, FormulaStringTable.MIN, FormulaStringTable.AVG, FormulaStringTable.MEDIAN };

	Map<String, String> descriptionMap = new HashMap<>();

	public MultiAggregateFormulaFactory() {
		initializeDescriptions();
	}

	private void initializeDescriptions() {
		descriptionMap.put(FormulaStringTable.SUM, FormulaStringTable.SUM_DESC);
		descriptionMap.put(FormulaStringTable.MAX, FormulaStringTable.MAX_DESC);
		descriptionMap.put(FormulaStringTable.MIN, FormulaStringTable.MIN_DESC);
		descriptionMap.put(FormulaStringTable.AVG, FormulaStringTable.AVG_DESC);
		descriptionMap.put(FormulaStringTable.MEDIAN, FormulaStringTable.MEDIAN_DESC);
	}

	public MultiFormulaAggregate getFormula(String formulaType, AggregateFormula formula, FormulaValueProvider valueProvider) {
		if (formulaType.equals(FormulaStringTable.SUM)) {
			return new SumFunctionFormula(formula, valueProvider);
		} else if (formulaType.equals(FormulaStringTable.MAX)) {
			return new MaxFunctionFormula(formula, valueProvider);
		} else if (formulaType.equals(FormulaStringTable.MIN)) {
			return new MinFunctionFormula(formula, valueProvider);
		} else if (formulaType.equals(FormulaStringTable.AVG)) {
			return new AverageFunctionFormula(formula, valueProvider);
		} else if (formulaType.equals(FormulaStringTable.MEDIAN)) {
			return new MedianFunctionFormula(formula, valueProvider);
		}
		return null;
	}

	public String[] getFormulaTypes() {
		return formulaTypes;
	}

	public String[] getDescriptions() {
		String[] descriptions = new String[formulaTypes.length];
		for (int i = 0; i < formulaTypes.length; i++) {
			if (descriptionMap.containsKey(formulaTypes[i])) {
				descriptions[i] = descriptionMap.get(formulaTypes[i]);
			} else {
				descriptions[i] = "";
			}
		}
		return descriptions;
	}

	public String getDescription(String formulaType) {
		if (descriptionMap.containsKey(formulaType)) {
			return descriptionMap.get(formulaType);
		} else {
			return "";
		}
	}
}
