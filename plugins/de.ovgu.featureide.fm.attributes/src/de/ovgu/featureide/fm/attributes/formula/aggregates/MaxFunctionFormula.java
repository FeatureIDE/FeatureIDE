package de.ovgu.featureide.fm.attributes.formula.aggregates;

import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.attributes.formula.AggregateFormula;
import de.ovgu.featureide.fm.attributes.formula.provider.FormulaValueProvider;

public class MaxFunctionFormula implements MultiFormulaAggregate {

	AggregateFormula formula;
	FormulaValueProvider valueProvider;
	private final static String TYPE = "Max";

	public MaxFunctionFormula(AggregateFormula formula, FormulaValueProvider valueProvider) {
		this.formula = formula;
		this.valueProvider = valueProvider;
	}

	@Override
	public double getResult(Iterable<? extends Object> valueHolders) {
		Double max = null;
		for (Object valueHolder : valueHolders) {
			Set<String> variables = formula.getVariables();
			Double current = 0d;
			if (formula instanceof MultiFormulaAggregate) {
				current = ((MultiFormulaAggregate) formula).getResult((Iterable<? extends Object>) valueHolder); // TODO: Safe
			} else {
				current = formula.getResult(valueProvider.getValues(valueHolder, variables.toArray(new String[variables.size()])));
			}
			if (current != null && (max == null || current > max)) {
				max = current;
			}
		}
		return max;
	}

	@Override
	public String toString() {
		String description = "Max:{" + formula.toString() + "}";
		return description;
	}

	@Override
	public Set<String> getVariables() {
		return formula.getVariables();
	}

	@Override
	public Double getResult(Map<String, Double> valueProviderMap) {
		// TODO Auto-generated method stub
		return 0d;
	}

	@Override
	public String getUnit(Map<String, String> unitProviderMap) {
		// TODO Auto-generated method stub
		return formula.getUnit(unitProviderMap);
	}

	@Override
	public String getType() {
		// TODO Auto-generated method stub
		return TYPE;
	}

	@Override
	public AggregateFormula getUnderlyingFunction() {
		return formula;
	}

	@Override
	public FormulaValueProvider getFormulaValueProvider() {
		return valueProvider;
	}

}
