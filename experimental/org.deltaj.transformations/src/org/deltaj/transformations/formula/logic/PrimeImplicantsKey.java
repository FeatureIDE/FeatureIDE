package org.deltaj.transformations.formula.logic;

class PrimeImplicantsKey implements Comparable<PrimeImplicantsKey> {

	private final int dontCareCount;
	private final int trueCount;

	public PrimeImplicantsKey(Term term) {

		dontCareCount = term.getCount(TermValue.DONTCARE);
		trueCount = term.getCount(TermValue.TRUE);
	}

	public PrimeImplicantsKey(int dontCareCount, int trueCount) {

		this.dontCareCount = dontCareCount;
		this.trueCount = trueCount;
	}

	@Override
	public int compareTo(PrimeImplicantsKey other) {

		int cmp = dontCareCount - other.dontCareCount;
		if (cmp != 0) {
			return cmp;
		}

		return trueCount - other.trueCount;
	}
}
