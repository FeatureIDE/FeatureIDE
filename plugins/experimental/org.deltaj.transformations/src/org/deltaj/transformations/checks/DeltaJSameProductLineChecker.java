package org.deltaj.transformations.checks;

import org.deltaj.deltaj.Feature;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJSameProductLineChecker {

	public void check(Feature featureA, Feature featureB) {

		if (DeltaJHierarchy.getProductLine(featureA) != DeltaJHierarchy.getProductLine(featureB)) {
			throw new DeltaJException(
					"Features '%s' and '%s' do not belong to the same product line.",
					featureA.getName(),
					featureB.getName());
		}
	}
}
