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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Random;

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
		variables = mapping;
		this.clauses = new ClauseList(clauses);
	}

	public CNF(Variables mapping) {
		variables = mapping;
		clauses = new ClauseList();
	}

	public CNF(List<LiteralSet> clauses) {
		variables = new Variables();
		this.clauses = new ClauseList(clauses);
	}

	/**
	 * Copy constructor. <br/> Also copies clause list (no deep copy).
	 */
	public CNF(CNF oldSatInstance) {
		this(oldSatInstance, true);
	}

	/**
	 * Copy constructor. <br/> Can either copy or neglect old clauses (no deep copy).
	 */
	public CNF(CNF oldSatInstance, boolean copyClauses) {
		variables = oldSatInstance.variables.clone();
		clauses = copyClauses ? new ClauseList(oldSatInstance.clauses) : new ClauseList();
	}

	public void addClause(LiteralSet clause) {
		clauses.add(clause);
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

	/**
	 * @return whether this CNF was sliced by an instance of {@code CNFSlicer}.
	 */
	public boolean isSliced() {
		return variables instanceof SlicedVariables;
	}

	/**
	 * If the CNF was sliced, the old variable IDs are kept for compatibility reasons. This method changes the the variable IDs in the variables object and the
	 * clause list, as if the CNF was not sliced.
	 *
	 * @return A new instance with a proper clause list and variables object, is this CNF was sliced. Returns {@code this}, otherwise.
	 *
	 * @see #isSliced()
	 */
	public CNF normalize() {
		if (isSliced()) {
			final SlicedVariables slicedVariables = (SlicedVariables) variables;
			final ClauseList newClauses = new ClauseList(clauses.size());
			for (final LiteralSet literalSet : clauses) {
				newClauses.add(variables.convertToInternal(literalSet));
			}
			final ArrayList<String> names = new ArrayList<>(variables.size());
			for (int i = 0; i < variables.intToVar.length; i++) {
				if (slicedVariables.orgToInternal[i] != 0) {
					names.add(variables.intToVar[i]);
				}
			}
			return new CNF(new Variables(names), newClauses);
		} else {
			return this;
		}
	}

	public ClauseList getClauses() {
		return clauses;
	}

	@Override
	public CNF clone() {
		return new CNF(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + ((clauses == null) ? 0 : clauses.hashCode());
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
		final CNF other = (CNF) obj;
		if (clauses == null) {
			if (other.clauses != null) {
				return false;
			}
		} else if (!clauses.equals(other.clauses)) {
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
		return "CNF\n\tvariables=" + variables + "\n\tclauses=" + clauses;
	}

	public CNF randomize(Random random) {
		final List<String> shuffledVars = Arrays.asList(Arrays.copyOf(variables.intToVar, variables.intToVar.length));
		Collections.shuffle(shuffledVars, random);
		final Variables shuffledVariables = new Variables(shuffledVars);

		final ArrayList<LiteralSet> newClauses = new ArrayList<>(clauses.size());
		for (final LiteralSet oldClause : clauses) {
			final int[] oldLiterals = oldClause.getLiterals();
			final int[] newLiterals = new int[oldLiterals.length];
			for (int i = 0; i < oldLiterals.length; i++) {
				final int l = oldLiterals[i];
				newLiterals[i] = shuffledVariables.getVariable(variables.getName(l), l > 0);
			}
			newClauses.add(new LiteralSet(newLiterals));
		}
		Collections.shuffle(newClauses, random);

		return new CNF(shuffledVariables, newClauses);
	}

}
