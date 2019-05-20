package de.ovgu.featureide.fm.attributes.formula.aggregates;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.attributes.formula.AggregateFormula;
import de.ovgu.featureide.fm.attributes.formula.provider.FormulaValueProvider;

public class MedianFunctionFormula implements MultiFormulaAggregate {

	AggregateFormula formula;
	FormulaValueProvider valueProvider;
	private final static String TYPE = "Median";

	public MedianFunctionFormula(AggregateFormula formula, FormulaValueProvider valueProvider) {
		this.formula = formula;
		this.valueProvider = valueProvider;
	}

	@Override
	public Double getResult(Map<String, Double> valueProviderMap) {
		// TODO Auto-generated method stub
		return 0d;
	}

	@Override
	public double getResult(Iterable<? extends Object> valueHolders) {
		Double sum = 0d;
		List<Double> values = new ArrayList<>();
		for (Object valueHolder : valueHolders) {
			Set<String> variables = formula.getVariables();
			Double current = 0d;
			if (formula instanceof MultiFormulaAggregate) {
				current = ((MultiFormulaAggregate) formula).getResult((Iterable<? extends Object>) valueHolder); // TODO: Safe
			} else {
				current = formula.getResult(valueProvider.getValues(valueHolder, variables.toArray(new String[variables.size()])));
			}
			if (current != null) {
				values.add(current);
			}

		}

		return computeMedianOfList(values);
	}

	private double computeMedianOfList(List<Double> values) {
		if (values.size() == 1) {
			return values.get(0);
		}
		Collections.sort(values);
		int midIndex = values.size() / 2;
		if (values.size() % 2 == 0) {
			return values.get(midIndex);
		} else {
			return values.get(midIndex - 1);
		}
	}

	@Override
	public Set<String> getVariables() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String toString() {
		String description = "Median(" + formula.toString() + ")";
		return description;
	}

	@Override
	public String getUnit(Map<String, String> unitProviderMap) {
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
