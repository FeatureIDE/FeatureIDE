package org.deltaj.transformations.facade;

public interface DeltaJTransformationsFacade
		extends DeltaJRenamingEntities, DeltaJExtractingDeltaActions, DeltaJResolvingDeltaActions,
		DeltaJMergingDeltaModules, DeltaJCleanupFeatures, DeltaJCleanupDeltaModules, DeltaJSimplifyingFormulas,
		DeltaJRefactoringFeatureConfigurations {

	DeltaJTransformationsFacade INSTANCE = DeltaJTransformationsFacadeFactory.create();
}
