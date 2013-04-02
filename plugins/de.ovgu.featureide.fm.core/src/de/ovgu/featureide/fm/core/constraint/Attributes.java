package de.ovgu.featureide.fm.core.constraint;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

public class Attributes<T> {

	private Map<String, Map<String, FeatureAttribute<T>>> attrs = new HashMap<String, Map<String, FeatureAttribute<T>>>();

	public boolean hasAttribute(String featureName, String attributeName) {
		return attrs.containsKey(attributeName) && attrs.get(attributeName).containsKey(featureName);
	}

	public boolean hasAttribute(FeatureAttribute<T> fa) {
		return hasAttribute(fa.getFeatureName(), fa.getAttributeName());
	}

	public FeatureAttribute<T> getAttribute(String featureName, String attributeName) {
		return hasAttribute(featureName, attributeName) ? attrs.get(attributeName).get(featureName) : null;
	}

	public void setAttribute(String featureName, String attributeName, T value) {
		if (!attrs.containsKey(attributeName))
			attrs.put(attributeName, new HashMap<String, FeatureAttribute<T>>());
		
		attrs.get(attributeName).put(featureName, new FeatureAttribute<T>(attributeName, featureName, value));
	}

	public void setAttribute(FeatureAttribute<T> fa) {
		if (!attrs.containsKey(fa.getAttributeName()))
			attrs.put(fa.getAttributeName(), new HashMap<String, FeatureAttribute<T>>());
		
		attrs.get(fa.getAttributeName()).put(fa.getFeatureName(),fa);
	}

	public Collection<FeatureAttribute<T>> getAttributes(String attributeName) {
		return attrs.get(attributeName).values();
	}
}
