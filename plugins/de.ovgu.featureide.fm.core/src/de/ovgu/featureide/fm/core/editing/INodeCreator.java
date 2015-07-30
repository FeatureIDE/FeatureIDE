/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.core.editing;

import org.prop4j.Or;

import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Takes a feature model as input and returns a propositional formula
 * representing the valid feature combinations.
 * 
 * @author Sebastian Krieter
 */
public interface INodeCreator<T> {

	/**
	 * Returns a propositional formula of a given feature model.
	 * 
	 * @param featureModel the feature model
	 * 
	 * @return all clauses of the CNF.
	 */
	T createNodes(FeatureModel featureModel);

	/**
	 * Returns a propositional formula of a given feature model, which only contains dependencies from the feature diagram's structure.
	 * 
	 * @param featureModel the feature model
	 * 
	 * @return a list of all {@link Or}s of the CNF.
	 */
	T createStructuralNodes(FeatureModel featureModel);

	/**
	 * Returns a propositional formula of a given feature model, which only contains dependencies from the feature diagram's constraints.
	 * 
	 * @param featureModel the feature model
	 * 
	 * @return a list of all {@link Or}s of the CNF.
	 */
	T createConstraintNodes(FeatureModel featureModel);

}
