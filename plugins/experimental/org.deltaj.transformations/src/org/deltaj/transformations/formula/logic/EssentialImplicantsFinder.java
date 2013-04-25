package org.deltaj.transformations.formula.logic;

import java.util.Set;
import java.util.TreeSet;

class EssentialImplicantsFinder {

	private final Set<Term> primeImplicants;
	private final Set<Term> essentialImplicants;
	private final ImplicationMap implicationMap;

	public EssentialImplicantsFinder(LogicFormula formula) {

		primeImplicants = new PrimeImplicantsFinder(formula).find();
		essentialImplicants = new TreeSet<Term>();
		implicationMap = new ImplicationMap(formula, primeImplicants);
	}

	public final Set<Term> find() {

		addUniqueImplicants();

		while (!implicationMap.getAllTerms().isEmpty()) {
			addBiggestImplicant();
		}

		return essentialImplicants;
	}

	private void addBiggestImplicant() {

		Term implicant = findBiggestImplicant();

//		System.out.printf("using biggest implicant %s\n", implicant);
		essentialImplicants.add(implicant);
		implicationMap.removeImplications(implicant);
	}

	private Term findBiggestImplicant() {

		int maxSize = 0;
		Term biggestImplicant = null;

		for (Term implicant: implicationMap.getAllImplicants()) {

			int size = implicationMap.getImpliedTerms(implicant).size();
//			System.out.printf("size of %s: -> %s\n", implicant, new Imploder(this.implicationMap.getImpliedTerms(implicant)).implode(" "));

			if (size > maxSize) {
				maxSize = size;
				biggestImplicant = implicant;
			}
		}

		return biggestImplicant;
	}

	private void addUniqueImplicants() {

		for (Term term: implicationMap.getAllTerms()) {
			Set<Term> implicants = implicationMap.getImplicantsOfTerm(term);
			if (implicants.size() == 1) {
//				System.out.printf("unique implicant %s -> %s\n", implicants.iterator().next(), term);
				essentialImplicants.addAll(implicants);
			}
		}

		for (Term implicant: essentialImplicants) {
			implicationMap.removeImplications(implicant);
		}
	}
}
