/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.conversion;

import java.util.List;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Interface for a conversion strategy.
 *
 * @author Alexander Knueppel
 */
public interface IConverterStrategy {

	/**
	 * Converts a feature model with complex constraints to a feature model with only requires- and excludes-constraints.
	 *
	 * @param fm Original feature model
	 * @param nodes List of (complex) formulas
	 * @param preserve States whether configuration semantics should be preserved (same number of configurations in original and converted model)
	 * @return Converted feature model
	 */
	public IFeatureModel convert(IFeatureModel fm, List<Node> nodes, boolean preserve);

	/**
	 * Should strive to simplify a complex constraint.
	 *
	 * @param constraint
	 * @return A list of nodes; some of them might be simple constraints
	 */
	public List<Node> preprocess(IConstraint constraint);
}
