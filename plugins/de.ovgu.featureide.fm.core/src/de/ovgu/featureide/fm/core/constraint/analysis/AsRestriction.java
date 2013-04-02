package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;

import de.ovgu.featureide.fm.core.constraint.RelationOperator;

public class AsRestriction extends Restriction {
	
	public AsRestriction(List<Term> terms, RelationOperator op, int degree) {
		super(terms, op, degree);
	}
	
	protected void init(List<Term> terms, RelationOperator op, int degree) {
		this.terms = makeDefensiveCopy(terms);
		this.op = op == RelationOperator.EQUAL ? Op.EQ : Op.GEQ;
		this.degree = degree;
		
		// if operator is "<=", multiply with (-1) to get ">="
		if (op == RelationOperator.LESS_EQUAL) {
			negateBothSides();
		}
		makeVarsPositive();
		sortById();
	}
	
	public boolean fid2asid(AtomicSets atomicSets) {
		Multimap<Integer, Term> termsByAsId = HashMultimap.create();
		
		for (Term term : terms) {
			termsByAsId.put(atomicSets.fid2As(term.getId()), term);
		}
		
		List<Term> groupedTerms = new ArrayList<Term>();
		for (int asId: termsByAsId.keySet()) {
			// sum up new merged coefficient
			int groupedCoefficient = 0;
			for (Term term : termsByAsId.get(asId)) {
				groupedCoefficient += term.getCoefficient();
			}
			// if coefficient unequal 0, replace old terms with new merged term
			if (groupedCoefficient != 0) {
				Term groupedTerm = new Term(asId, groupedCoefficient, true);
				groupedTerms.add(groupedTerm);
			}
			
		}

		terms = groupedTerms;
		
		return isSatisfied();
	}
	
	public boolean simplify(Collection<Integer> oldIds, Integer newId) {
		// collect restrictions affected by the merge, sum up new coefficient
		List<Term> groupedTerms = new ArrayList<Term>();
		int groupedCoefficient = 0;
		for (Term term : terms) {
			if (oldIds.contains(term.getId())) {
				groupedTerms.add(term);
				groupedCoefficient += term.getCoefficient();
			}
		}
		
		// remove the old terms, will be replaced by a merged term
		terms.removeAll(groupedTerms);
		
		// set new term
		if (groupedCoefficient != 0) {
			Term groupedTerm = new Term(newId, groupedCoefficient, true);
			terms.add(groupedTerm);
		}
		
		return isSatisfied(); 
	}
	
	protected boolean isSatisfied() {
		if (terms.size() == 0) {
			if (op == Op.EQ && degree == 0 || op == Op.GEQ && degree <= 0) {
				return true;
			} else {
				throw new RuntimeException("simpflified restriction leads "
						+ "to contradiction");
			}
		}
		
		return false;
	}
}
