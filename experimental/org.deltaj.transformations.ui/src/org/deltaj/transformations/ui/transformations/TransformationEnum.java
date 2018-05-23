package org.deltaj.transformations.ui.transformations;

import org.deltaj.transformations.ui.transformation.ITransformationCommandHandler;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public enum TransformationEnum {
	RENAME_ELEMENT(new RenameElement()),

	EXTRACT_DELTA_ACTION(new ExtractDeltaAction()),
	EXTRACT_MATCHING_ACTIONS(new ExtractMatchingActions()),

	RESOLVE_REMOVAL_ACTION(new ResolveRemovalAction()),
	RESOLVE_MODIFICATION_ACTION(new ResolveModificationAction()),

	MERGE_COMPATIBLE_DELTA_MODULES(new MergeModulesWithEquivalenConditions()),
	MERGE_DELTA_MODULES_WITH_INVERSES(new MergeDeltaModulesWithInverses()),

	SIMPLIFY_APPLICATION_CONDITIONS(new SimplifyApplicationConditions()),
	SIMPLIFY_FEATURE_CONFIGURATIONS(new SimplifyFeatureConfigurations()),
	MERGE_CONFIGURATIONS_INTO_CONDITIONS(new MergeConfigurationsIntoConditions()),

	REMOVE_FEATUE(new RemoveFeature()),
	REMOVE_UNUSED_FEATURES(new RemoveUnusedFeatures()),
	REMOVE_PRODUCT(new RemoveProduct()),
	REMOVE_DELTA_ACTION(new RemoveDeltaAction()),
	REMOVE_DELTA_MODULE(new RemoveDeltaModule()),
	REMOVE_EMPTY_DELTA_MODULES(new RemoveEmptyDeltaModules());

	private final ITransformationCommandHandler handler;

	private TransformationEnum(ITransformationCommandHandler handler) {

		this.handler = handler;
	}

	public ITransformationCommandHandler getCommandHandler() {

		return handler;
	}

	public static TransformationEnum getByCommandId(String commandId) {

		TransformationEnum transformationEnum = TransformationEnum.valueOf(commandId);

		if (transformationEnum == null) {
			throw new DeltaJException("Failed to find transformation enum for command id '%s'.", commandId);
		}

		return transformationEnum;
	}
}
