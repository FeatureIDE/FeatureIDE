package org.deltaj.transformations.formula;

import java.util.ArrayList;
import java.util.Set;
import org.deltaj.deltaj.Feature;

public class FeatureList extends ArrayList<Feature> {

	public Set<Feature> getEnabledFeaturesFor(int configuration) {

		Set<Feature> enabledFeatures = new FeatureSet();

		int n = size();
		for (int index = 0; index < n; ++index) {
			int mask = 1 << index;
			if ((configuration & mask) != 0) {
				enabledFeatures.add(get(index));
			}
		}

		return enabledFeatures;
	}
}
