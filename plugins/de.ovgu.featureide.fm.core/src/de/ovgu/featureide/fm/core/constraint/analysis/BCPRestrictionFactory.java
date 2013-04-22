/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.Collection;
import java.util.List;

import de.ovgu.featureide.fm.core.constraint.RelationOperator;

/**
 * TODO description
 */
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