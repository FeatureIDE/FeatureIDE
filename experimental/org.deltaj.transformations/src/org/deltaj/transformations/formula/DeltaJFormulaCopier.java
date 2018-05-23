package org.deltaj.transformations.formula;

import org.deltaj.deltaj.And;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.Negation;
import org.deltaj.deltaj.Or;
import org.deltaj.deltaj.PropFalse;
import org.deltaj.deltaj.PropParen;
import org.deltaj.deltaj.PropTrue;
import org.deltaj.deltaj.PropositionalFormula;
import org.eclipse.xtext.util.PolymorphicDispatcher;

public class DeltaJFormulaCopier {

	private final DeltajFactory factory;
	private final PolymorphicDispatcher<PropositionalFormula> dispatcher;

	public DeltaJFormulaCopier() {

		this.factory = DeltajFactory.eINSTANCE;
		this.dispatcher = PolymorphicDispatcher.createForSingleTarget("copyDispatch", 1, 1, this);
	}

	public PropositionalFormula copy(PropositionalFormula formula) {

		return formula != null? dispatcher.invoke(formula) : null;
	}

	// -------------------- DISPATCHED METHODS -------------------- //

	protected PropositionalFormula copyDispatch(@SuppressWarnings("unused") PropTrue propTrue) {

		return factory.createPropTrue();
	}

	protected PropositionalFormula copyDispatch(@SuppressWarnings("unused") PropFalse propFalse) {

		return factory.createPropFalse();
	}

	protected PropositionalFormula copyDispatch(And and) {

		And newAnd = factory.createAnd();
		newAnd.setLeft(copy(and.getLeft()));
		newAnd.setRight(copy(and.getRight()));
		return newAnd;
	}

	protected PropositionalFormula copyDispatch(Or or) {

		Or newOr = factory.createOr();
		newOr.setLeft(copy(or.getLeft()));
		newOr.setRight(copy(or.getRight()));
		return newOr;
	}

	protected PropositionalFormula copyDispatch(Negation negation) {

		Negation newNegation = factory.createNegation();
		newNegation.setFormula(copy(negation.getFormula()));
		return newNegation;
	}

	protected PropositionalFormula copyDispatch(PropParen paren) {

		PropParen newParen = factory.createPropParen();
		newParen.setFormula(copy(paren.getFormula()));
		return newParen;
	}

	protected PropositionalFormula copyDispatch(FeatureRef ref) {

		FeatureRef newRef = factory.createFeatureRef();
		newRef.setFeature(ref.getFeature());
		return newRef;
	}
}
