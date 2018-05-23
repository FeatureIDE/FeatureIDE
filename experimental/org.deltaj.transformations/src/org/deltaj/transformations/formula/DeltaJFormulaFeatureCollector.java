package org.deltaj.transformations.formula;

import java.util.Collections;
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
import org.eclipse.xtext.util.PolymorphicDispatcher;

public class DeltaJFormulaFeatureCollector {

	private final PolymorphicDispatcher<Set<Feature>> dispatcher;

	public DeltaJFormulaFeatureCollector() {

		this.dispatcher = PolymorphicDispatcher.createForSingleTarget("collectFeatures", 1, 1, this);
	}

	public Set<Feature> collect(PropositionalFormula formula) {

		return formula != null? dispatcher.invoke(formula) : Collections.<Feature> emptySet();
	}

	protected Set<Feature> collectFeatures(And and) {

		Set<Feature> features = new FeatureSet();
		features.addAll(collect(and.getLeft()));
		features.addAll(collect(and.getRight()));
		return features;
	}

	protected Set<Feature> collectFeatures(Or or) {

		Set<Feature> features = new FeatureSet();
		features.addAll(collect(or.getLeft()));
		features.addAll(collect(or.getRight()));
		return features;
	}

	protected Set<Feature> collectFeatures(Negation negate) {

		return collect(negate.getFormula());
	}

	protected Set<Feature> collectFeatures(PropParen paren) {

		return collect(paren.getFormula());
	}

	protected Set<Feature> collectFeatures(FeatureRef ref) {

		return Collections.singleton(ref.getFeature());
	}

	@SuppressWarnings("unused")
	protected Set<Feature> collectFeatures(PropTrue propTrue) {

		return Collections.emptySet();
	}

	@SuppressWarnings("unused")
	protected Set<Feature> collectFeatures(PropFalse propFalse) {

		return Collections.emptySet();
	}
}
