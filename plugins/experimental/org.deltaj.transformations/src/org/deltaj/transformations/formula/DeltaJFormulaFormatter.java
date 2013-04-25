package org.deltaj.transformations.formula;

import org.deltaj.deltaj.And;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.Negation;
import org.deltaj.deltaj.Or;
import org.deltaj.deltaj.PropFalse;
import org.deltaj.deltaj.PropParen;
import org.deltaj.deltaj.PropTrue;
import org.deltaj.deltaj.PropositionalFormula;
import org.eclipse.xtext.util.PolymorphicDispatcher;

public class DeltaJFormulaFormatter {

	private final PolymorphicDispatcher<String> dispatcher;

	public DeltaJFormulaFormatter() {

		this.dispatcher = PolymorphicDispatcher.createForSingleTarget("formatDispatch", 1, 1, this);
	}

	public String format(PropositionalFormula formula) {

		return dispatcher.invoke(formula);
	}

	// -------------------- DISPATCHED METHODS -------------------- //

	protected String formatDispatch(@SuppressWarnings("unused") PropTrue propTrue) {

		return "true";
	}

	protected String formatDispatch(@SuppressWarnings("unused") PropFalse propFalse) {

		return "false";
	}

	protected String formatDispatch(And and) {

		StringBuilder builder = new StringBuilder();
		builder.append(format(and.getLeft()));
		builder.append(" && ");
		builder.append(format(and.getRight()));
		return builder.toString();
	}

	protected String formatDispatch(Or or) {

		StringBuilder builder = new StringBuilder();
		builder.append(format(or.getLeft()));
		builder.append(" || ");
		builder.append(format(or.getRight()));
		return builder.toString();
	}

	protected String formatDispatch(Negation negation) {

		StringBuilder builder = new StringBuilder();
		builder.append("!");
		builder.append(format(negation.getFormula()));
		return builder.toString();
	}

	protected String formatDispatch(PropParen paren) {

		StringBuilder builder = new StringBuilder();
		builder.append("(");
		builder.append(format(paren.getFormula()));
		builder.append(")");
		return builder.toString();
	}

	protected String formatDispatch(FeatureRef ref) {

		return ref.getFeature().getName();
	}
}
