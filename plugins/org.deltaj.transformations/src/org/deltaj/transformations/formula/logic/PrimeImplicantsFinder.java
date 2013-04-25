package org.deltaj.transformations.formula.logic;

import java.util.Set;
import java.util.TreeSet;

class PrimeImplicantsFinder {

	private final LogicFormula formula;
	private final Set<Term> terms;
	private final PrimeImplicantsMap map;

	public PrimeImplicantsFinder(LogicFormula formula) {

		this.formula = formula;
		terms = new TreeSet<Term>(formula.getTerms());
		map = new PrimeImplicantsMap();
	}

	public Set<Term> find() {

		fillMap();

		int n = formula.getVariableCount();
		for (int dontCareCount = 0; dontCareCount < n; ++dontCareCount) {
			for (int trueCount = 0; trueCount < n; ++trueCount) {
				Set<Term> termsLess = map.getTerms(dontCareCount, trueCount);
				Set<Term> termsMore = map.getTerms(dontCareCount, trueCount + 1);
				merge(termsLess, termsMore);
			}
		}

		return terms;
	}

	private void merge(Set<Term> termsLess, Set<Term> termsMore) {

		for (Term less: termsLess) {
			for (Term more: termsMore) {
				Term mergedTerm = less.mergeIfPossible(more);
				if (mergedTerm != null) {
//					System.out.printf("merging %s and %s -> %s\n", less, more, mergedTerm);
					terms.remove(less);
					terms.remove(more);
					terms.add(mergedTerm);

					map.add(mergedTerm);
				}
			}
		}
	}

	private void fillMap() {

		for (Term term: terms) {
			map.add(term);
		}
	}
}
