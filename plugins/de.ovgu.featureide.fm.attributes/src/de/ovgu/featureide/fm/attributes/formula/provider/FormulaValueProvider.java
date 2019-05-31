package de.ovgu.featureide.fm.attributes.formula.provider;

import java.util.Map;

public interface FormulaValueProvider {
	
	public Map<String, Double> getValues(Object obj, String[] values);
	
	public Map<String, String> getUnits(Object obj, String[] values);
	
	public Double getDefaultValue();
}
