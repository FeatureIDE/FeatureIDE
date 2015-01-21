package org.deltaj.transformations.evolution;

import org.deltaj.deltaj.And;
import org.deltaj.deltaj.Configuration;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.Features;
import org.deltaj.deltaj.Negation;
import org.deltaj.deltaj.Or;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.PropFalse;
import org.deltaj.deltaj.PropParen;
import org.deltaj.deltaj.PropTrue;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.finder.feature.DeltaJConfigurationsWithFeatureFinder;
import org.deltaj.transformations.finder.feature.references.DeltaJModuleReferencesWithFeatureFinder;
import org.deltaj.transformations.finder.product.DeltaJProductsWithFeatureFinder;
import org.deltaj.transformations.formula.DeltaJFormulaBuilder;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.ListUtils;
import org.eclipse.xtext.util.PolymorphicDispatcher;

public class DeltaJFeatureRemover {

	private final DeltaJFormulaBuilder formulaBuilder;
	private final PolymorphicDispatcher<PropositionalFormula> dispatcher;
	private final Feature feature;
	private final Features features;

	public DeltaJFeatureRemover(Feature feature) {

		this.formulaBuilder = new DeltaJFormulaBuilder();
		this.dispatcher = PolymorphicDispatcher.createForSingleTarget("_removeFromFormula", 1, 1, this);
		this.feature = feature;
		this.features = DeltaJHierarchy.getFeatures(feature);
	}

	public void remove() {

		removeFromFormulas();

		removeFromProducts();

		ListUtils.removeElementByIdentity(features.getFeaturesList(), feature);
	}

	private void removeFromFormulas() {

		for (Configuration configuration: new DeltaJConfigurationsWithFeatureFinder(feature).find()) {
			configuration.setFormula(removeFromFormula(configuration.getFormula()));
		}

		for (ModuleReference moduleReference: new DeltaJModuleReferencesWithFeatureFinder(feature).find()) {
			moduleReference.setWhen(removeFromFormula(moduleReference.getWhen()));
		}
	}

	private void removeFromProducts() {

		for (Product product: new DeltaJProductsWithFeatureFinder(feature).find()) {
			ListUtils.removeElementByIdentity(product.getFeatures(), feature);
		}
	}

	private PropositionalFormula removeFromFormula(PropositionalFormula formula) {

		return dispatcher.invoke(formula);
	}

	// ------------------------------ DISPATCHING ------------------------------ //

	protected PropositionalFormula _removeFromFormula(And and) {

		return formulaBuilder.and(removeFromFormula(and.getLeft()), removeFromFormula(and.getRight()));
	}

	protected PropositionalFormula _removeFromFormula(Or or) {

		return formulaBuilder.or(removeFromFormula(or.getLeft()), removeFromFormula(or.getRight()));
	}

	protected PropositionalFormula _removeFromFormula(Negation negate) {

		return formulaBuilder.not(removeFromFormula(negate.getFormula()));
	}

	protected PropositionalFormula _removeFromFormula(PropParen paren) {

		return removeFromFormula(paren.getFormula());
	}

	protected PropositionalFormula _removeFromFormula(FeatureRef ref) {

		if (ref.getFeature() == feature) {
			return formulaBuilder.createFalse();
		} else {
			return ref;
		}
	}

	protected PropositionalFormula _removeFromFormula(PropFalse propFalse) {

		return propFalse;
	}

	protected PropositionalFormula _removeFromFormula(PropTrue propTrue) {

		return propTrue;
	}
}
