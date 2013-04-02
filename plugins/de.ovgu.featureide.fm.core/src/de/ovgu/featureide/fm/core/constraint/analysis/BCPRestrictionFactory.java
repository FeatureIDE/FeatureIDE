package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.Collection;
import java.util.List;

import de.ovgu.featureide.fm.core.constraint.RelationOperator;

public class BCPRestrictionFactory implements RestrictionFactory<AeRestriction> {

	private AssignmentRegistry registry;
	
	private RelationOperator LEQ = RelationOperator.LESS_EQUAL;
	
	private RelationOperator EQ = RelationOperator.EQUAL;
	
	private RelationOperator GEQ = RelationOperator.GREATER_EQUAL;
	
	public BCPRestrictionFactory(AssignmentRegistry registry) {
		this.registry = registry;
	}
	
	@Override
	public void createAndAdd(List<Term> terms, RelationOperator op,
			int degree, Collection<AeRestriction> restrictions) {
		
		if (op == LEQ || op == EQ) {
			restrictions.add(new AeRestriction(registry, terms, LEQ, degree));
		}
		if (op == GEQ || op == EQ) {
			restrictions.add(new AeRestriction(registry, terms, GEQ, degree));
		}
	}

}