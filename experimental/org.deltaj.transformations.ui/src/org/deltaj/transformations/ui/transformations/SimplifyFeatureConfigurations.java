package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.Configuration;
import org.deltaj.transformations.simplify.DeltaJFeatureConfigurationSimplifier;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

public class SimplifyFeatureConfigurations extends AbstractTransformationCommandHandler {

	public SimplifyFeatureConfigurations() {

		super(
				"Simplify Feature Configurations",
				IconEnum.CONFIGURATIONS,
				"Tries to simplify the feature configurations.");
	}

	void transform(Configuration configuration) {

		new DeltaJFeatureConfigurationSimplifier(configuration).simplify();
	}
}
