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

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.IConstraint;

/**
 * @brief Converter using conjunctive normal form.
 *
 * @author Alexander Knueppel
 */
public class CNFConverter extends NNFConverter {

	/**
	 * Constructor
	 */
	public CNFConverter() {
		super();
		// continues number + level
		naming.put(Or.class, "Clause%d");
		topName = "SubtreeCNF";
	}

	/**
	 * Creates cnf and returns a list of clauses
	 */
	@Override
	public List<Node> preprocess(IConstraint constraint) {
		final List<Node> clauses = new LinkedList<Node>();

		final Node cnf = constraint.getNode().toCNF();

		if (cnf instanceof And) {
			clauses.addAll(Arrays.asList(cnf.getChildren()));
		} else {
			clauses.add(cnf);
		}

		return clauses;
	}
}
