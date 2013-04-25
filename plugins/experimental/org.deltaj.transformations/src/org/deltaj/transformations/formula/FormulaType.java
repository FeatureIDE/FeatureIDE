package org.deltaj.transformations.formula;

import org.deltaj.deltaj.And;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.Negation;
import org.deltaj.deltaj.Or;
import org.deltaj.deltaj.PropFalse;
import org.deltaj.deltaj.PropParen;
import org.deltaj.deltaj.PropTrue;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public enum FormulaType {

	AND,
	OR,
	NOT,
	PARENTHESES,
	FEATURE,
	TRUE,
	FALSE;

	public static FormulaType get(PropositionalFormula formula) {

		if (formula instanceof And) {
			return AND;
		} else if (formula instanceof Or) {
			return OR;
		} else if (formula instanceof Negation) {
			return NOT;
		} else if (formula instanceof PropParen) {
			return PARENTHESES;
		} else if (formula instanceof FeatureRef) {
			return FEATURE;
		} else if (formula instanceof PropTrue) {
			return TRUE;
		} else if (formula instanceof PropFalse) {
			return FALSE;
		} else {
			throw new DeltaJException("Invalid formula type '%s'.", formula.getClass().getName());
		}
	}
}
