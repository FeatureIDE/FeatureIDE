package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.Collection;
import java.util.List;

import de.ovgu.featureide.fm.core.constraint.RelationOperator;

public class DeRestrictionFactory implements RestrictionFactory<DeRestriction> {

	@Override
	public void createAndAdd(List<Term> terms, RelationOperator op,
			int degree,  Collection<DeRestriction> restrictions) {
		restrictions.add(new DeRestriction(terms, op, degree));
	}

}
