package de.ovgu.featureide.fm.attributes.formula;

import java.util.Map;
import java.util.Set;

public interface AggregateFormula {

	public Double getResult(Map<String, Double> valueProviderMap);
	
	public Set<String> getVariables();
	
	public String getUnit(Map<String, String> unitProviderMap);
	
	public String getType();
}
