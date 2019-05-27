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
				result += (char) sign + "(" + factors.get(i).toString() + ")";
			} else {
				result += (char) sign + factors.get(i).toString();
			}

		}

		result = result.substring(1, result.length());
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
