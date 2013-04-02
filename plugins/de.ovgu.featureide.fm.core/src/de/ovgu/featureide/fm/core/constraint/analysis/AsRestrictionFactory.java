package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.Collection;
import java.util.List;

import de.ovgu.featureide.fm.core.constraint.RelationOperator;

public class AsRestrictionFactory implements RestrictionFactory<AsRestriction> {

	@Override
	public void createAndAdd(List<Term> terms, RelationOperator op,
			int degree, Collection<AsRestriction> restrictions) {
		 restrictions.add(new AsRestriction(terms, op, degree));
	}

}