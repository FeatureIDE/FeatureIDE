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
