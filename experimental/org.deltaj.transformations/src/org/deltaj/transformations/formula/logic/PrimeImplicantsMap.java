package org.deltaj.transformations.formula.logic;

import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

class PrimeImplicantsMap {

	private final Map<PrimeImplicantsKey, Set<Term>> map;

	public PrimeImplicantsMap() {

		map = new TreeMap<PrimeImplicantsKey, Set<Term>>();
	}

	public void add(Term term) {

		PrimeImplicantsKey key = new PrimeImplicantsKey(term);

		Set<Term> set = map.get(key);
		if (set == null) {
			map.put(key, set = new TreeSet<Term>());
		}

		set.add(term);
	}

	public Set<Term> getTerms(int dontCareCount, int trueCount) {

		PrimeImplicantsKey key = new PrimeImplicantsKey(dontCareCount, trueCount);
		Set<Term> matchingTerms = map.get(key);
		return matchingTerms != null? matchingTerms : Collections.<Term> emptySet();
	}
}
