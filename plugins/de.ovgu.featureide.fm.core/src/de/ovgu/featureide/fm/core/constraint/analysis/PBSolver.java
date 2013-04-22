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
import java.util.Set;

/**
 * The PBSolver interface encapsulates the functionality of a pseudo boolean
 * satisfiability solver. Each class that implements this interface can 
 * be plugged in to reason on extended feature models.
 * 
 * @author Sebastian Henneberg
 */
public interface PBSolver {

	/**
	 * Adds a restriction to the pseudo boolean satisfiability solver.
	 * 
	 * @param <T> The concrete type of the restriction.
	 * @param restriction The restriction to add.
	 */
	public <T extends Restriction> void addRestriction(T restriction);
	
	/**
	 * Adds restrictions to the pseudo boolean satisfiability solver.
	 * 
	 * @param <T> The concrete type of the restrictions.
	 * @param restrictions The restrictions to add.
	 */
	public <T extends Restriction> void addRestrictions(
			Collection<T> restrictions);
	
	/**
	 * Is the currently submitted set of restrictions satisfiable?
	 * 
	 * @return True if there is at least one satisfying assignments, false 
	 * otherwise.
	 */
	public boolean isSatisfiable();
	
	/**
	 * Is the currently submitted set of restrictions satisfiable with respect 
	 * of the passed assumptions?
	 * 
	 * @param assumptions An array of temporary assumption used for this call.
	 * @return True if there is at least one satisfying assignments, false 
	 * otherwise.
	 */
	public boolean isSatisfiable(int[] assumptions);
	
	/**
	 * Verifies if the passed variables are either true or false for all 
	 * satisfying assignments. Returns +id for each true assignments and 
	 * -id for each false assignment in the resulting set. In general, the 
	 * resulting set contains fewer elements than the input set because some 
	 * variables are not yet statically assigned.
	 * 
	 * @param varibales The indices of the variables to examine.
	 * @return Those variables that are statically assigned and their assignment. 
	 */
	public Set<Integer> backbone(Set<Integer> varibales);
}
