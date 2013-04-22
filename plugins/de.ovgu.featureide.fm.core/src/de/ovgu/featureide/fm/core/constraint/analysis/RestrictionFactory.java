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
 * The different feature model analysis operations need different concrete
 * implementations to reason on the input date. This interface of an abstract 
 * factory enables to use a general translation utility that builds restrictions
 * out of a feature model and additional constraints. 
 * 
 * @author Sebastian Henneberg
 *
 * @param <T> The concrete type of the restriction.
 */
public interface RestrictionFactory<T> {

	/**
	 * Creates a new restriction equivalent but not identical to the arguments. 
	 * 
	 * @param terms Linear term used on the left side of the restriction.
	 * @param op The operator which is either LEQ, EQ or GEQ. 
	 * @param degree The degree is an integer number on the right hand side.
	 * @param restrictions The collection where the new restriction will be stored.
	 * @return An instance representing an equivalent restriction.
	 */
	void createAndAdd(List<Term> terms, RelationOperator op, int degree, 
			Collection<T> restrictions);
	
}
