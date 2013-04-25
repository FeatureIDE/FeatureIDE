package org.deltaj.transformations.formula;

import org.deltaj.deltaj.And;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.Negation;
import org.deltaj.deltaj.PropositionalFormula;

class TermBuilder {

	private final DeltajFactory factory;
	private PropositionalFormula term;

	public TermBuilder(DeltajFactory factory) {

		this.factory = factory;
		this.term = null;
	}

	public void addTrue(Feature feature) {

		FeatureRef featureRef = createFeatureRef(feature);
		add(featureRef);
	}

	public void addFalse(Feature feature) {

		FeatureRef featureRef = createFeatureRef(feature);
		Negation negation = createNegation(featureRef);
		add(negation);
	}

	private void add(PropositionalFormula variable) {

		if (term == null) {
			term = variable;
		} else {
			term = createAnd(term, variable);
		}
	}

	private FeatureRef createFeatureRef(Feature feature) {

		FeatureRef featureRef = factory.createFeatureRef();
		featureRef.setFeature(feature);
		return featureRef;
	}

	private Negation createNegation(PropositionalFormula childFormula) {

		Negation negation = factory.createNegation();
		negation.setFormula(childFormula);
		return negation;
	}

	private And createAnd(PropositionalFormula left, PropositionalFormula right) {

		And and = factory.createAnd();
		and.setLeft(left);
		and.setRight(right);
		return and;
	}

	public PropositionalFormula getTerm() {

		return term != null? term : factory.createPropTrue();
	}
}
