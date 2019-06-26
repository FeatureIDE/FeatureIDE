package de.ovgu.featureide.fm.attributes.formula.aggregates;

import java.util.Set;

import de.ovgu.featureide.fm.attributes.formula.AggregateFormula;
import de.ovgu.featureide.fm.attributes.formula.provider.FormulaValueProvider;

public interface MultiFormulaAggregate extends AggregateFormula {

	public double getResult(Iterable<? extends Object> valueHolders);

	public Set<String> getVariables();

	public AggregateFormula getUnderlyingFunction();

	public FormulaValueProvider getFormulaValueProvider();
}
