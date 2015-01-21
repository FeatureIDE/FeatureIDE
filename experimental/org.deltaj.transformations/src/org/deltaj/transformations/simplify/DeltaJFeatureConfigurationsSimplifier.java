package org.deltaj.transformations.simplify;

import org.deltaj.deltaj.Configuration;
import org.deltaj.deltaj.ProductLine;

public class DeltaJFeatureConfigurationsSimplifier {

	public void simplify(ProductLine productLine) {

		for (Configuration configuration: productLine.getConfigurations().getConfigurations()) {
			new DeltaJFeatureConfigurationSimplifier(configuration).simplify();
		}
	}
}
