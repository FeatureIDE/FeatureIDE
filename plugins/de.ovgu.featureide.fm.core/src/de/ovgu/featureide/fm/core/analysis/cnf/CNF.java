/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * Represents an instance of a satisfiability problem in CNF.
 * 
 * @author Sebastian Krieter
 */
public class CNF implements Serializable {

	private static final long serialVersionUID = -5140589732063007073L;

	protected final ClauseList clauses;
	protected final Variables variables;

	public CNF(Variables mapping, List<LiteralSet> clauses) {
		this.variables = mapping;
		this.clauses = new ClauseList(clauses);
	}

	public CNF(Variables mapping) {
		this.variables = mapping;
		this.clauses = new ClauseList();
	}

	/**
	 * Copy constructor. <br/>
	 * Also copies clause list (no deep copy).
	 */
	public CNF(CNF oldSatInstance) {
		this(oldSatInstance, true);
	}

	/**
	 * Copy constructor. <br/>
	 * Can either copy or neglect old clauses (no deep copy).
	 */
	public CNF(CNF oldSatInstance, boolean copyClauses) {
		this.variables = oldSatInstance.variables.clone();
		this.clauses = copyClauses ? new ClauseList(oldSatInstance.clauses) : new ClauseList();
	}

	public void addClause(LiteralSet clause) {
		this.clauses.add(clause);
	}

	public void addClauses(Collection<LiteralSet> clauses) {
		this.clauses.addAll(clauses);
	}

	public IVariables getVariables() {
		return variables;
	}

	public IInternalVariables getInternalVariables() {
		return variables;
	}

	public List<LiteralSet> getClauses() {
		return Collections.unmodifiableList(clauses);
	}

	@Override
	public CNF clone() {
		return new CNF(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((clauses == null) ? 0 : clauses.hashCode());
		result = prime * result + ((variables == null) ? 0 : variables.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		CNF other = (CNF) obj;
		if (clauses == null) {
			if (other.clauses != null)
				return false;
		} else if (!clauses.equals(other.clauses))
			return false;
		if (variables == null) {
			if (other.variables != null)
				return false;
		} else if (!variables.equals(other.variables))
			return false;
		return true;
	}

}
