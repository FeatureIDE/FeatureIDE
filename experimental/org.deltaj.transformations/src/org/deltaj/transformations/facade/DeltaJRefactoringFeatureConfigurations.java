package org.deltaj.transformations.facade;

import org.deltaj.deltaj.ProductLine;

public interface DeltaJRefactoringFeatureConfigurations {

	void mergeConfigurationsIntoConditions(ProductLine productLine);

	void extractConfigurationsFromConditions(ProductLine productLine);
}
