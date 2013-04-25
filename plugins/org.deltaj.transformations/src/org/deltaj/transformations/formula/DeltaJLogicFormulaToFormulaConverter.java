package org.deltaj.transformations.formula;

import java.util.List;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Or;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.formula.logic.LogicFormula;
import org.deltaj.transformations.formula.logic.Term;
import org.deltaj.transformations.formula.logic.TermValue;

public class DeltaJLogicFormulaToFormulaConverter {

	private final DeltajFactory factory;
	private final LogicFormula logicFormula;
	private final List<Feature> features;

	public DeltaJLogicFormulaToFormulaConverter(LogicFormula logicFormula, List<Feature> features) {

		this.factory = DeltajFactory.eINSTANCE;
		this.logicFormula = logicFormula;
		this.features = features;
	}

	public PropositionalFormula convert() {

		if (logicFormula.isFalse()) {
			return factory.createPropFalse();
		} else if (logicFormula.isTrue()) {
			return factory.createPropTrue();
		}

		return convertTerms();
	}

	private PropositionalFormula convertTerms() {

		PropositionalFormula formula = null;

		for (Term term: logicFormula.getTerms()) {

			PropositionalFormula termFormula = convert(term);

			if (formula == null) {
				formula = termFormula;
			} else {
				formula = createOr(formula, termFormula);
			}
		}

		return formula != null? formula : factory.createPropFalse();
	}

	private Or createOr(PropositionalFormula left, PropositionalFormula right) {

		Or or = factory.createOr();
		or.setLeft(left);
		or.setRight(right);
		return or;
	}

	private PropositionalFormula convert(Term term) {

		TermBuilder termBuilder = new TermBuilder(factory);

		for (int index = 0; index < logicFormula.getVariableCount(); ++index) {

			Feature feature = features.get(index);

			if (term.getValue(index) == TermValue.TRUE) {
				termBuilder.addTrue(feature);
			} else if (term.getValue(index) == TermValue.FALSE) {
				termBuilder.addFalse(feature);
			}
		}

		return termBuilder.getTerm();
	}
}
