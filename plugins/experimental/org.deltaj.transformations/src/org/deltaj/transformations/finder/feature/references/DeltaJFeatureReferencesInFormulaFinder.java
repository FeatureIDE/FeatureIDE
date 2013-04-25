package org.deltaj.transformations.finder.feature.references;

import java.util.List;
import org.deltaj.deltaj.And;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.Negation;
import org.deltaj.deltaj.Or;
import org.deltaj.deltaj.PropFalse;
import org.deltaj.deltaj.PropParen;
import org.deltaj.deltaj.PropTrue;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.utils.ListFactory;
import org.eclipse.xtext.util.PolymorphicDispatcher;

public class DeltaJFeatureReferencesInFormulaFinder {

	private final PolymorphicDispatcher<Void> dispatcher;
	private final List<FeatureRef> references;
	private final PropositionalFormula formula;

	public DeltaJFeatureReferencesInFormulaFinder(PropositionalFormula formula) {

		this.dispatcher = PolymorphicDispatcher.createForSingleTarget("_collect", 1, 1, this);
		this.references = ListFactory.createArrayList();
		this.formula = formula;
	}

	public List<FeatureRef> find() {

		references.clear();

		collect(formula);

		return references;
	}

	protected void collect(PropositionalFormula formula) {

		dispatcher.invoke(formula);
	}

	protected void _collect(And and) {

		collect(and.getLeft());
		collect(and.getRight());
	}

	protected void _collect(Or or) {

		collect(or.getLeft());
		collect(or.getRight());
	}

	protected void _collect(Negation negation) {

		collect(negation.getFormula());
	}

	protected void _collect(PropParen propParen) {

		collect(propParen.getFormula());
	}

	protected void _collect(FeatureRef featureRef) {

		references.add(featureRef);
	}

	protected void _collect(@SuppressWarnings("unused") PropTrue propTrue) {

		// nothing to do
	}

	protected void _collect(@SuppressWarnings("unused") PropFalse propFalse) {

		// nothing to do
	}
}
