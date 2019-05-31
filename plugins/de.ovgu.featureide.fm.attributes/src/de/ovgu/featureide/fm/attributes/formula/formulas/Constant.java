package de.ovgu.featureide.fm.attributes.formula.formulas;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.attributes.formula.AggregateFormula;

public class Constant implements AggregateFormula {

	double value;
	private final static String TYPE = "Constant";
	
	public Constant(double value) {
		this.value = value;
	}
	
	@Override
	public Double getResult(Map<String, Double> valueProviderMap) {
		return value;
	}

	@Override
	public Set<String> getVariables() {
		return new HashSet<String>();
	}

	@Override
	public String toString() {
		return String.valueOf(value);
	}

	@Override
	public String getUnit(Map<String, String> unitProviderMap) {
		return "";
	}
	
	@Override
	public String getType() {
		// TODO Auto-generated method stub
		return TYPE;
	}

}
