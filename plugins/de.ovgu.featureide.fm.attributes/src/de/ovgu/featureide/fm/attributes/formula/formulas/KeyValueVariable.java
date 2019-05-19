package de.ovgu.featureide.fm.attributes.formula.formulas;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.attributes.formula.AggregateFormula;

public class KeyValueVariable implements AggregateFormula {
	
	String name;
	private final static String TYPE = "Variable";
	public KeyValueVariable(String name) {
		this.name = name;
	}
	
	@Override
	public Double getResult(Map<String, Double> valueProviderMap) {
		return valueProviderMap.get(name);
	}
	
	@Override
	public String toString() {
		return "\"" + name + "\"";
	}

	@Override
	public Set<String> getVariables() {
		Set<String> variable = new HashSet<String>();
		variable.add(name);
		return variable;
	}

	@Override
	public String getUnit(Map<String, String> unitProviderMap) {
		// TODO Auto-generated method stub
		return unitProviderMap.get(name);
	}
	
	@Override
	public String getType() {
		// TODO Auto-generated method stub
		return TYPE;
	}

}
