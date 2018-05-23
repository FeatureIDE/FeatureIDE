package org.deltaj.transformations.formula.logic;

import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

class ImplicationMap {

	private final LogicFormula formula;
	private final Set<Term> primeImplicants;
	private final Map<Term, Set<Term>> termToImplicants;
	private final Map<Term, Set<Term>> implicantToTerms;

	public ImplicationMap(LogicFormula formula, Set<Term> implicants) {

		this.formula = formula;
		primeImplicants = implicants;
		termToImplicants = new TreeMap<Term, Set<Term>>();
		implicantToTerms = new TreeMap<Term, Set<Term>>();

		for (Term primeImplicant: primeImplicants) {
			for (Term term: this.formula.getTerms()) {
				if (primeImplicant.implies(term)) {
					addImplication(primeImplicant, term);
				}
			}
		}
	}

	private void addImplication(Term implicant, Term term) {

		Set<Term> implicants = termToImplicants.get(term);
		if (implicants == null) {
			termToImplicants.put(term, implicants = new TreeSet<Term>());
		}
		implicants.add(implicant);

		Set<Term> terms = implicantToTerms.get(implicant);
		if (terms == null) {
			implicantToTerms.put(implicant, terms = new TreeSet<Term>());
		}
		terms.add(term);
	}

	public Set<Term> getAllTerms() {

		return Collections.unmodifiableSet(termToImplicants.keySet());
	}

	public Set<Term> getAllImplicants() {

		return Collections.unmodifiableSet(implicantToTerms.keySet());
	}

	public Set<Term> getImplicantsOfTerm(Term term) {

		Set<Term> implicants = termToImplicants.get(term);
		return implicants != null? Collections.unmodifiableSet(implicants) : Collections.<Term> emptySet();
	}

	public Set<Term> getImpliedTerms(Term implicant) {

		Set<Term> terms = implicantToTerms.get(implicant);
		return terms != null? Collections.unmodifiableSet(terms) : Collections.<Term> emptySet();
	}

	public void removeImplications(Term implicant) {

		Set<Term> terms = new TreeSet<Term>(getImpliedTerms(implicant));

		for (Term term: terms) {
			removeMappingToTerm(term);
			removeMappingFromTerm(term);
		}
	}

	private void removeMappingToTerm(Term term) {

		for (Term implicant: getImplicantsOfTerm(term)) {
			implicantToTerms.get(implicant).remove(term);
		}
	}

	private void removeMappingFromTerm(Term term) {

		termToImplicants.remove(term);
	}
}
