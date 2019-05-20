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
