package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.Collection;
import java.util.List;

import de.ovgu.featureide.fm.core.constraint.RelationOperator;

public class AeRestrictionFactory implements RestrictionFactory<AeRestriction> {

	private RelationOperator LEQ = RelationOperator.LESS_EQUAL;
	
	private RelationOperator EQ = RelationOperator.EQUAL;
	
	private RelationOperator GEQ = RelationOperator.GREATER_EQUAL;
	
	@Override
	public void createAndAdd(List<Term> terms, RelationOperator op,
			int degree,  Collection<AeRestriction> restrictions) {
		
		if (op == LEQ || op == EQ) {
			restrictions.add(new AeRestriction(terms, LEQ, degree));
		}
		if (op == GEQ || op == EQ) {
			restrictions.add(new AeRestriction(terms, GEQ, degree));
		}
	}
}
