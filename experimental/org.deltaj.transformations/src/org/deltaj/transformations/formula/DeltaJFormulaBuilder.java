package org.deltaj.transformations.formula;

import org.deltaj.deltaj.And;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.Negation;
import org.deltaj.deltaj.Or;
import org.deltaj.deltaj.PropFalse;
import org.deltaj.deltaj.PropParen;
import org.deltaj.deltaj.PropTrue;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.exceptions.DeltaJIllegalEnumConstant;

public class DeltaJFormulaBuilder {

	private final DeltajFactory factory;

	public DeltaJFormulaBuilder() {

		this.factory = DeltajFactory.eINSTANCE;
	}

	public PropositionalFormula optimize(PropositionalFormula formula) {

		return new DeltaJFormulaOptimizer(formula).optimize();
	}

	public PropositionalFormula copy(PropositionalFormula formula) {

		return new DeltaJFormulaCopier().copy(formula);
	}

	public And and(PropositionalFormula left, PropositionalFormula right) {

		PropositionalFormula parenthesesLeft = putIntoParenthesesIfNecessary(left);
		PropositionalFormula parenthesesRight = putIntoParenthesesIfNecessary(right);

		And and = factory.createAnd();
		and.setLeft(parenthesesLeft);
		and.setRight(parenthesesRight);
		return and;
	}

	public Or or(PropositionalFormula left, PropositionalFormula right) {

		PropositionalFormula parenthesesLeft = putIntoParenthesesIfNecessary(left);
		PropositionalFormula parenthesesRight = putIntoParenthesesIfNecessary(right);

		Or or = factory.createOr();
		or.setLeft(parenthesesLeft);
		or.setRight(parenthesesRight);
		return or;
	}

	public Negation not(PropositionalFormula formula) {

		PropositionalFormula parentheses = putIntoParenthesesIfNecessary(formula);

		Negation negation = factory.createNegation();
		negation.setFormula(parentheses);
		return negation;
	}

	public PropFalse createFalse() {

		return factory.createPropFalse();
	}

	public PropTrue createTrue() {

		return factory.createPropTrue();
	}

	private PropositionalFormula putIntoParenthesesIfNecessary(PropositionalFormula formula) {

		FormulaType formulaType = FormulaType.get(formula);

		switch (formulaType) {
		case AND:
		case OR:
			return putIntoParentheses(formula);
		case NOT:
		case FEATURE:
		case PARENTHESES:
		case TRUE:
		case FALSE:
			return formula;
		}

		throw new DeltaJIllegalEnumConstant(formulaType);
	}

	private PropParen putIntoParentheses(PropositionalFormula formula) {

		PropParen parentheses = factory.createPropParen();
		parentheses.setFormula(formula);
		return parentheses;
	}
}
