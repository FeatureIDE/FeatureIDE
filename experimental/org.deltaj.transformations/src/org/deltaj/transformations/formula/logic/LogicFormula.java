package org.deltaj.transformations.formula.logic;

import java.util.Collections;
import java.util.Set;
import java.util.TreeSet;
import org.deltaj.transformations.utils.Imploder;

public class LogicFormula {

	private final static int MAX_VARIABLE_COUNT = 10;
	private final Boolean constant;
	private final byte variableCount;
	private final Set<Term> terms;

	public LogicFormula(boolean constant) {

		this.constant = constant;
		this.variableCount = 0;
		this.terms = null;
	}

	public LogicFormula(int variableCount) {

		if (variableCount < 0 || variableCount > MAX_VARIABLE_COUNT) {
			throw new IllegalArgumentException(String.format("Illegal variable count %d, it must be in the range [0, %d].", variableCount, MAX_VARIABLE_COUNT));
		}

		this.constant = null;
		this.variableCount = (byte) variableCount;
		this.terms = new TreeSet<Term>();
	}

	private LogicFormula(byte variableCount, Set<Term> terms) {

		this.constant = getConstant(terms);
		this.variableCount = constant == null? variableCount : 0;
		this.terms = constant == null? new TreeSet<Term>(terms) : null;
	}

	private Boolean getConstant(Set<Term> terms) {

		if (terms.isEmpty()) {
			return false;
		}

		if (terms.size() == 1 && terms.iterator().next().isTautology()) {
			return true;
		}

		return null;
	}

	public void addTerm(int configuration) {

		terms.add(Term.fromConfiguration(variableCount, configuration));
	}

	public void addTerm(String termText) {

		terms.add(Term.parse(variableCount, termText));
	}

	public LogicFormula convertToPrimeImplicants() {

		if (constant != null) {
			return this;
		}

		Set<Term> newTerms = new PrimeImplicantsFinder(this).find();
		return new LogicFormula(variableCount, newTerms);
	}

	public LogicFormula minimize() {

		if (constant != null) {
			return this;
		}

		Set<Term> newTerms = new EssentialImplicantsFinder(this).find();
		return new LogicFormula(variableCount, newTerms);
	}

	@Override
	public String toString() {

		if (constant != null) {
			return "" + constant;
		}

		return new Imploder(getTerms()).implode(" + ");
	}

	public int getVariableCount() {

		return variableCount;
	}

	public Set<Term> getTerms() {

		return Collections.unmodifiableSet(terms);
	}

	public boolean isTrue() {

		return constant != null && constant == true;
	}

	public boolean isFalse() {

		return constant != null && constant == false;
	}
}
