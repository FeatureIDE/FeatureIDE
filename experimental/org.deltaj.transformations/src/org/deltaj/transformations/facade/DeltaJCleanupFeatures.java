package org.deltaj.transformations.facade;

import org.deltaj.deltaj.Feature;

public interface DeltaJCleanupFeatures {

	void removeEmptyFeature(Feature feature);

	void removeUnusedFeature(Feature feature);

	void mergeDuplicatedFeatures(Feature featureA, Feature featureB, String mergedName);

	void mergeJoinedFeatures(Feature featureA, Feature featureB, String mergedName);
}
