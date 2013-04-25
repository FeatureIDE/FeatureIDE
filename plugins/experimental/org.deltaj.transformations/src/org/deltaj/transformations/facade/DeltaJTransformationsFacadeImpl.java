package org.deltaj.transformations.facade;

import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.deltaj.Configuration;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.cleanup.features.DeltaJDuplicatedFeaturesMerger;
import org.deltaj.transformations.cleanup.features.DeltaJEmptyFeatureRemover;
import org.deltaj.transformations.cleanup.features.DeltaJJoinedFeaturesMerger;
import org.deltaj.transformations.cleanup.features.DeltaJUnusedFeatureRemover;
import org.deltaj.transformations.conditions.DeltaJConfigurationsIntoAllApplicationConditionsMerger;
import org.deltaj.transformations.extract.DeltaJActionExtractor;
import org.deltaj.transformations.extract.DeltaJConflictingActionsExtractor;
import org.deltaj.transformations.merge.DeltaJAllModulesWithEquivalentConditionsMerger;
import org.deltaj.transformations.merge.DeltaJModulesWithEquivalentConditionsMerger;
import org.deltaj.transformations.merge.DeltaJModulesWithEquivalentConditionsOfPartitionPartMerger;
import org.deltaj.transformations.merge.DeltaJModulesWithInverseMerger;
import org.deltaj.transformations.rename.DeltaJFeatureRenamer;
import org.deltaj.transformations.rename.DeltaJModuleRenamer;
import org.deltaj.transformations.rename.DeltaJProductLineRenamer;
import org.deltaj.transformations.rename.DeltaJProductRenamer;
import org.deltaj.transformations.resolve.DeltaJModificationActionResolver;
import org.deltaj.transformations.resolve.DeltaJModificationActionsResolver;
import org.deltaj.transformations.resolve.DeltaJRemovalActionResolver;
import org.deltaj.transformations.resolve.DeltaJRemovalActionsResolver;
import org.deltaj.transformations.simplify.DeltaJApplicationConditionSimplifier;
import org.deltaj.transformations.simplify.DeltaJApplicationConditionsSimplifier;
import org.deltaj.transformations.simplify.DeltaJFeatureConfigurationSimplifier;
import org.deltaj.transformations.simplify.DeltaJFeatureConfigurationsSimplifier;

/**
 * This implementation of the {@link DeltaJTransformationsFacade} simply
 * delegates the method calls to the respective transformation classes.
 * 
 * @author Oliver Richers
 */
class DeltaJTransformationsFacadeImpl implements DeltaJTransformationsFacade {

	@Override
	public void renameDeltaModule(DeltaModule deltaModule, String newName) {

		new DeltaJModuleRenamer(deltaModule, newName).rename();
	}

	@Override
	public void renameFeature(Feature feature, String newName) {

		new DeltaJFeatureRenamer(feature, newName).rename();
	}

	@Override
	public void renameProduct(Product product, String newName) {

		new DeltaJProductRenamer(product, newName).rename();
	}

	@Override
	public void renameProductLine(ProductLine productLine, String newName) {

		new DeltaJProductLineRenamer(productLine, newName).rename();
	}

	@Override
	public void extractDeltaAction(DeltaAction deltaAction) {

		new DeltaJActionExtractor(deltaAction).extract();
	}

	@Override
	public void extractMatchingActions(DeltaModule deltaModuleA, DeltaModule deltaModuleB) {

		new DeltaJConflictingActionsExtractor(deltaModuleA, deltaModuleB).extract();
	}

	@Override
	public void resolveDuplicatedAction(DeltaAction deltaActionA, DeltaAction deltaActionB) {

		// TODO
	}

	@Override
	public void resolveMethodModificationAction(MethodModification methodModification) {

		new DeltaJModificationActionResolver(methodModification).resolve();
	}

	@Override
	public void resolveMethodModificationActions(ProductLine productLine) {

		new DeltaJModificationActionsResolver().resolve(productLine);
	}

	@Override
	public void resolveRemovalAction(ClassRemoval classRemoval) {

		new DeltaJRemovalActionResolver(classRemoval).resolve();
	}

	@Override
	public void resolveRemovalAction(MethodRemoval methodRemoval) {

		new DeltaJRemovalActionResolver(methodRemoval).resolve();
	}

	@Override
	public void resolveRemovalAction(FieldRemoval fieldRemoval) {

		new DeltaJRemovalActionResolver(fieldRemoval).resolve();
	}

	@Override
	public void resolveRemovalActions(ProductLine productLine) {

		new DeltaJRemovalActionsResolver().resolve(productLine);
	}

	@Override
	public void mergeDeltaModulesWithEquivalentConditions(DeltaModule deltaModuleA, DeltaModule deltaModuleB) {

		new DeltaJModulesWithEquivalentConditionsMerger(deltaModuleA, deltaModuleB).merge();
	}

	@Override
	public void mergeDeltaModulesWithEquivalentConditions(PartitionPart partitionPart) {

		new DeltaJModulesWithEquivalentConditionsOfPartitionPartMerger(partitionPart).merge();
	}

	@Override
	public void mergeDeltaModulesWithEquivalentConditions(ProductLine productLine) {

		new DeltaJAllModulesWithEquivalentConditionsMerger().merge(productLine);
	}

	@Override
	public void mergeDeltaModulesWithEquivalentContent(DeltaModule deltaModuleA, DeltaModule deltaModuleB) {

		// TODO
	}

	@Override
	public void mergeDeltaModulesWithEquivalentContent(ProductLine productLine) {

		// TODO
	}

	@Override
	public void mergeDeltaModulesWithInverse(DeltaModule deltaModuleA, DeltaModule deltaModuleB) {

		new DeltaJModulesWithInverseMerger(deltaModuleA, deltaModuleB).merge();
	}

	@Override
	public void removeEmptyFeature(Feature feature) {

		new DeltaJEmptyFeatureRemover(feature).remove();
	}

	@Override
	public void removeUnusedFeature(Feature feature) {

		new DeltaJUnusedFeatureRemover(feature).remove();
	}

	@Override
	public void mergeDuplicatedFeatures(Feature featureA, Feature featureB, String mergedName) {

		new DeltaJDuplicatedFeaturesMerger(featureA, featureB, mergedName).merge();
	}

	@Override
	public void mergeJoinedFeatures(Feature featureA, Feature featureB, String mergedName) {

		new DeltaJJoinedFeaturesMerger(featureA, featureB, mergedName).merge();
	}

	@Override
	public void mergeCompatiblePartitionParts(PartitionPart partitionPartA, PartitionPart partitionPartB) {

		// TODO Auto-generated method stub

	}

	@Override
	public void removeDeadDeltaAction(DeltaAction deltaAction) {

		// TODO Auto-generated method stub

	}

	@Override
	public void removeDeadDeltaAction(DeltaSubAction deltaSubAction) {

		// TODO Auto-generated method stub

	}

	@Override
	public void removeDeadDeltaModule(DeltaModule deltaModule) {

		// TODO Auto-generated method stub

	}

	@Override
	public void removeEmptyDeltaModule(DeltaModule deltaModule) {

		// TODO Auto-generated method stub

	}

	@Override
	public void simplifyApplicationCondition(ModuleReference moduleReference) {

		new DeltaJApplicationConditionSimplifier(moduleReference).simplify();
	}

	@Override
	public void simplifyApplicationConditions(ProductLine productLine) {

		new DeltaJApplicationConditionsSimplifier().simplify(productLine);
	}

	@Override
	public void simplifyFeatureConfiguration(Configuration configuration) {

		new DeltaJFeatureConfigurationSimplifier(configuration).simplify();
	}

	@Override
	public void simplifyFeatureConfigurations(ProductLine productLine) {

		new DeltaJFeatureConfigurationsSimplifier().simplify(productLine);
	}

	@Override
	public void mergeConfigurationsIntoConditions(ProductLine productLine) {

		new DeltaJConfigurationsIntoAllApplicationConditionsMerger().merge(productLine);
	}

	@Override
	public void extractConfigurationsFromConditions(ProductLine productLine) {

		// TODO Auto-generated method stub

	}
}
