package org.deltaj.transformations.cleanup.features;

import org.deltaj.deltaj.Feature;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJDuplicatedFeaturesChecker {

	private final Feature featureA;
	private final Feature featureB;

	public DeltaJDuplicatedFeaturesChecker(Feature featureA, Feature featureB) {

		this.featureA = featureA;
		this.featureB = featureB;
	}

	public boolean isDuplicated() {

		// TODO
		return true;
	}

	public void check() {

		if (!isDuplicated()) {

			throw new DeltaJException(
					"The features '%s' and '%s' are not duplicated.",
					featureA.getName(),
					featureB.getName());
		}
	}
}
