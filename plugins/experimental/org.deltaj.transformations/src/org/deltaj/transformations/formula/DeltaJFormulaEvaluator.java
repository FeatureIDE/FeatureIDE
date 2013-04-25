package org.deltaj.transformations.formula;

import java.util.Set;
import org.deltaj.deltaj.And;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.Negation;
import org.deltaj.deltaj.Or;
import org.deltaj.deltaj.PropFalse;
import org.deltaj.deltaj.PropParen;
import org.deltaj.deltaj.PropTrue;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.utils.SetFactory;
import org.eclipse.xtext.util.PolymorphicDispatcher;

public class DeltaJFormulaEvaluator {

	private final PropositionalFormula completeFormula;
	private final PolymorphicDispatcher<Boolean> dispatcher;
	private Set<Feature> enabledFeatures;

	public DeltaJFormulaEvaluator(PropositionalFormula formula) {

		this.completeFormula = formula;
		this.dispatcher = PolymorphicDispatcher.createForSingleTarget("evaluateFormula", 1, 1, this);
	}

	public boolean evaluate(String...enabledFeatures) {

		Set<Feature> features = new FeatureSet();
		Set<String> featureNames = SetFactory.createTreeSet(enabledFeatures);
		for (Feature feature: new DeltaJFormulaFeatureCollector().collect(completeFormula)) {
			if (featureNames.contains(feature.getName())) {
				features.add(feature);
			}
		}
		return evaluate(features);
	}

	public boolean evaluate(Set<Feature> enabledFeatures) {

		if (completeFormula == null) {
			return true;
		}

		this.enabledFeatures = enabledFeatures;

		return evaluate(completeFormula);
	}

	private boolean evaluate(PropositionalFormula formula) {

		return dispatcher.invoke(formula);
	}

	protected Boolean evaluateFormula(And and) {

		return evaluate(and.getLeft()) && evaluate(and.getRight());
	}

	protected Boolean evaluateFormula(Or or) {

		return evaluate(or.getLeft()) || evaluate(or.getRight());
	}

	protected Boolean evaluateFormula(Negation negate) {

		return !evaluate(negate.getFormula());
	}

	protected Boolean evaluateFormula(PropParen paren) {

		return evaluate(paren.getFormula());
	}

	protected Boolean evaluateFormula(FeatureRef ref) {

		return enabledFeatures.contains(ref.getFeature());
	}

	@SuppressWarnings("unused")
	protected Boolean evaluateFormula(PropTrue propTrue) {

		return true;
	}

	@SuppressWarnings("unused")
	protected Boolean evaluateFormula(PropFalse propFalse) {

		return false;
	}
}
