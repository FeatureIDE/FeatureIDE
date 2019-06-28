package de.ovgu.featureide.fm.attributes.formula.aggregates;

import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.attributes.formula.AggregateFormula;
import de.ovgu.featureide.fm.attributes.formula.provider.FormulaValueProvider;

public class SumFunctionFormula implements MultiFormulaAggregate {

	AggregateFormula formula;
	FormulaValueProvider valueProvider;
	private final static String TYPE = "Sum";

	public SumFunctionFormula(AggregateFormula formula, FormulaValueProvider valueProvider) {
		this.formula = formula;
		this.valueProvider = valueProvider;
	}

	@Override
	public Double getResult(Map<String, Double> valueProviderMap) {
		return 0d;
	}

	@Override
	public Set<String> getVariables() {
		return formula.getVariables();
	}

	@Override
	public double getResult(Iterable<? extends Object> valueHolders) {
		Double sum = 0d;
		for (Object valueHolder : valueHolders) {
			Set<String> variables = formula.getVariables();
			Double current = 0d;
			if (formula instanceof MultiFormulaAggregate) {
				current = ((MultiFormulaAggregate) formula).getResult((Iterable<? extends Object>) valueHolder); // TODO: Safe
			} else {
				current = formula.getResult(valueProvider.getValues(valueHolder, variables.toArray(new String[variables.size()])));
			}
			if (current != null) {
				sum += current;
			}

		}
		return sum;
	}

	@Override
	public String toString() {
		String description = "Sum(" + formula.toString() + ")";
		return description;
	}

	@Override
	public String getUnit(Map<String, String> unitProviderMap) {
		return formula.getUnit(unitProviderMap);
	}

	@Override
	public String getType() {
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
