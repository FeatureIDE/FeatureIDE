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
package de.ovgu.featureide.fm.core.analysis.cnf;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Represents an instance of a satisfiability problem in CNF.
 *
 * @author Sebastian Krieter
 */
public class SolutionList implements Serializable {

	private static final long serialVersionUID = 3882530497452645334L;

	protected final List<LiteralSet> solutions;
	protected Variables variables;

	public SolutionList() {
		solutions = new ArrayList<>();
	}

	public SolutionList(Variables mapping, List<LiteralSet> solutions) {
		variables = mapping;
		this.solutions = solutions;
	}

	public void addSolution(LiteralSet clause) {
		solutions.add(clause);
	}

	public void addSolutions(Collection<LiteralSet> clauses) {
		solutions.addAll(clauses);
	}

	public void setVariables(Variables variables) {
		this.variables = variables;
	}

	public Variables getVariables() {
		return variables;
	}

	public List<LiteralSet> getSolutions() {
		return solutions;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + ((solutions == null) ? 0 : solutions.hashCode());
		result = (prime * result) + ((variables == null) ? 0 : variables.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}
		final SolutionList other = (SolutionList) obj;
		if (solutions == null) {
			if (other.solutions != null) {
				return false;
			}
		} else if (!solutions.equals(other.solutions)) {
			return false;
		}
		if (variables == null) {
			if (other.variables != null) {
				return false;
			}
		} else if (!variables.equals(other.variables)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return "CNF\n\tvariables=" + variables + "\n\tsolutions=" + solutions;
	}

	public String getSolutionsString() {
		final StringBuilder sb = new StringBuilder();
		for (final LiteralSet clause : solutions) {
			sb.append("(");
			final List<String> literals = variables.convertToString(clause, true, true, true);
			for (final String literal : literals) {
				sb.append(literal);
				sb.append(", ");
			}
			if (!literals.isEmpty()) {
				sb.delete(sb.length() - 2, sb.length());
			}
			sb.append("), ");
		}
		if (!solutions.isEmpty()) {
			sb.delete(sb.length() - 2, sb.length());
		}
		return sb.toString();
	}

}
