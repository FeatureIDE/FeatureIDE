package org.deltaj.transformations.cleanup.features;

import org.deltaj.deltaj.Feature;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJJoinedFeaturesChecker {

	private final Feature featureA;
	private final Feature featureB;

	public DeltaJJoinedFeaturesChecker(Feature featureA, Feature featureB) {

		this.featureA = featureA;
		this.featureB = featureB;
	}

	public boolean isJoined() {

		// TODO
		return true;
	}

	public void check() {

		if (!isJoined()) {

			throw new DeltaJException(
					"The features '%s' and '%s' are not joined.",
					featureA.getName(),
					featureB.getName());
		}
	}
}
