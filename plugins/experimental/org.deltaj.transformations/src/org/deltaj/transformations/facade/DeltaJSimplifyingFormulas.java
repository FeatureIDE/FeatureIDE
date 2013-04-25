package org.deltaj.transformations.facade;

import org.deltaj.deltaj.Configuration;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.ProductLine;

public interface DeltaJSimplifyingFormulas {

	void simplifyApplicationCondition(ModuleReference moduleReference);

	void simplifyApplicationConditions(ProductLine productLine);

	void simplifyFeatureConfiguration(Configuration configuration);

	void simplifyFeatureConfigurations(ProductLine productLine);
}
