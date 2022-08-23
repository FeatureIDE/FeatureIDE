/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis.mig;

import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Variables;

/**
 * Computes a textual representation of the feature relationships in a modal implication graph.
 *
 * @author Sebastian Krieter
 */
public class MIGDependenciesWriter {

	public String write(final ModalImplicationGraph mig, final Variables variables) {
		final StringBuilder sb = new StringBuilder();
		sb.append("X ALWAYS Y := If X is selected then Y is selected in every valid configuration.\n");
		sb.append("X MAYBE  Y := If X is selected then Y is selected in at least one but not all valid configurations. \n");
		sb.append("X NEVER  Y := If X is selected then Y cannot be selected in any valid configuration.\n\n");

		final List<Vertex> adjList = mig.getAdjList();
		for (final Vertex vertex : adjList) {
			if (!vertex.isCore() && !vertex.isDead()) {
				final int var = vertex.getVar();
				if (var > 0) {
					final String name = variables.getName(var);
					for (final int otherVar : vertex.getStrongEdges()) {
						final Vertex otherVertex = mig.getVertex(otherVar);
						if (!otherVertex.isCore() && !otherVertex.isDead()) {
							sb.append(name);
							if (otherVar > 0) {
								sb.append(" ALWAYS ");
							} else {
								sb.append(" NEVER ");
							}
							sb.append(variables.getName(otherVar));
							sb.append("\n");
						}
					}
					for (final int clauseId : vertex.getComplexClauses()) {
						final LiteralSet clause = mig.getComplexClauses().get(clauseId);
						for (final int otherVar : clause.getLiterals()) {
							if ((otherVar > 0) && (var != otherVar)) {
								sb.append(name);
								sb.append(" MAYBE ");
								sb.append(variables.getName(otherVar));
								sb.append("\n");
							}
						}
					}
				}
			}
		}
		return sb.toString();
	}

}
