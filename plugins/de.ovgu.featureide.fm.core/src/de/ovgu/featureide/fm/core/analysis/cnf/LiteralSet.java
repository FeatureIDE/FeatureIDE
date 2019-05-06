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
import java.util.Arrays;
import java.util.TreeSet;

import javax.annotation.CheckForNull;

/**
 * A sorted list of literals. Can be used as a clause of a CNF or DNF.
 *
 * @author Sebastian Krieter
 */
public class LiteralSet implements Cloneable, Serializable, Comparable<LiteralSet> {

	private static final long serialVersionUID = 8948014814795787431L;

	protected final int[] literals;

	private final int hashCode;

	/**
	 * Constructs a new clause from the given literals. Negates the given literals. <br/> <b>Does not modify the given literal array.</b>
	 *
	 * @param literals literals of the clause
	 * @return A newly constructed clause from the given literals (negated).
	 */
	public static LiteralSet getBlockingClause(int... literals) {
		return new LiteralSet(SatUtils.negateSolution(literals));
	}

	/**
	 * Constructs a new clause from the given literals. <br/> <b>Does not modify the given literal array.</b>
	 *
	 * @param literals literals of the clause
	 * @return A newly constructed clause from the given literals.
	 */
	public static LiteralSet getClause(int... literals) {
		return new LiteralSet(SatUtils.negateSolution(literals));
	}

	/**
	 * Constructs a deep copy of the given clause.
	 *
	 * @param clause the old clause
	 */
	public LiteralSet(LiteralSet clause) {
		literals = Arrays.copyOf(clause.literals, clause.literals.length);
		hashCode = clause.hashCode;
	}

	/**
	 * Constructs a new clause from the given literals. <br/> <b>The resulting clause is backed by the given literal array. The array will be sorted.</b>
	 *
	 * @param literals literals of the clause
	 */
	public LiteralSet(int... literals) {
		this(literals, true);
	}

	protected LiteralSet(int[] literals, boolean sort) {
		this.literals = literals;
		if (sort) {
			Arrays.sort(this.literals);
		}
		hashCode = Arrays.hashCode(literals);
	}

	public int[] getLiterals() {
		return literals;
	}

	public boolean containsLiteral(int literal) {
		return indexOfLiteral(literal) >= 0;
	}

	public boolean containsVariable(int variable) {
		return indexOfVariable(variable) >= 0;
	}

	public int indexOfLiteral(int literal) {
		return Arrays.binarySearch(literals, literal);
	}

	public int indexOfVariable(int variable) {
		for (int i = 0; i < literals.length; i++) {
			if (Math.abs(literals[i]) == variable) {
				return i;
			}
		}
		return -1;
	}

	// TODO exploit that both sets are sorted
	public boolean containsAll(LiteralSet otherLiteralSet) {
		for (final int otherLiteral : otherLiteralSet.getLiterals()) {
			if (indexOfLiteral(otherLiteral) < 0) {
				return false;
			}
		}
		return true;
	}

	public int countNegative() {
		int count = 0;
		for (int i = 0; i < literals.length; i++) {
			if (literals[i] < 0) {
				count++;
			} else {
				break;
			}
		}
		return count;
	}

	public int countPositive() {
		int count = 0;
		for (int i = literals.length - 1; i >= 0; i--) {
			if (literals[i] > 0) {
				count++;
			} else {
				break;
			}
		}
		return count;
	}

	public int size() {
		return literals.length;
	}

	public LiteralSet getVariables() {
		final int[] absoluteLiterals = Arrays.copyOf(literals, literals.length);
		for (int i = 0; i < absoluteLiterals.length; i++) {
			absoluteLiterals[i] = Math.abs(absoluteLiterals[i]);
		}
		return new LiteralSet(absoluteLiterals);
	}

	public LiteralSet removeAll(LiteralSet variables) {
		final boolean[] removeMarker = new boolean[literals.length];
		final int count = getDuplicates(variables, removeMarker);

		final int[] newLiterals = new int[literals.length - count];
		int j = 0;
		for (int i = 0; i < literals.length; i++) {
			if (!removeMarker[i]) {
				newLiterals[j++] = literals[i];
			}
		}
		return new LiteralSet(newLiterals, false);
	}

	public LiteralSet retainAll(LiteralSet variables) {
		final boolean[] removeMarker = new boolean[literals.length];
		final int count = getDuplicates(variables, removeMarker);

		final int[] newLiterals = new int[count];
		int j = 0;
		for (int i = 0; i < literals.length; i++) {
			if (removeMarker[i]) {
				newLiterals[j++] = literals[i];
			}
		}
		return new LiteralSet(newLiterals, false);
	}

	// TODO exploit fact that variables and literals are sorted
	protected int getDuplicates(LiteralSet variables, final boolean[] removeMarker) {
		final int[] otherLiterals = variables.getLiterals();
		int count = 0;
		for (int i = 0; i < otherLiterals.length; i++) {
			final int index = indexOfLiteral(otherLiterals[i]);
			if (index >= 0) {
				count++;
				if (removeMarker != null) {
					removeMarker[index] = true;
				}
			}
		}
		return count;
	}

	public boolean hasDuplicates(LiteralSet variables) {
		final int[] otherLiterals = variables.getLiterals();
		for (int i = 0; i < otherLiterals.length; i++) {
			if (indexOfLiteral(otherLiterals[i]) >= 0) {
				return true;
			}
		}
		return false;
	}

	public int countDuplicates(LiteralSet variables) {
		return getDuplicates(variables, null);
	}

	public boolean hasConflicts(LiteralSet variables) {
		final int[] otherLiterals = variables.getLiterals();
		for (int i = 0; i < otherLiterals.length; i++) {
			if (indexOfLiteral(-otherLiterals[i]) >= 0) {
				return true;
			}
		}
		return false;
	}

	public int countConflicts(LiteralSet variables) {
		final int[] otherLiterals = variables.getLiterals();
		int count = 0;
		for (int i = 0; i < otherLiterals.length; i++) {
			if (indexOfLiteral(-otherLiterals[i]) >= 0) {
				count++;
			}
		}
		return count;
	}

	public LiteralSet negate() {
		final int[] negLiterals = Arrays.copyOf(literals, literals.length);
		final int highestIndex = negLiterals.length - 1;
		for (int i = 0; i < negLiterals.length; i++) {
			negLiterals[highestIndex - i] = -literals[i];
		}
		return new LiteralSet(negLiterals, false);
	}

	public LiteralSet getPositive() {
		return new LiteralSet(Arrays.copyOfRange(literals, literals.length - countPositive(), literals.length), false);
	}

	public LiteralSet getNegative() {
		return new LiteralSet(Arrays.copyOfRange(literals, 0, countNegative()), false);
	}

	/**
	 * Constructs a new {@link LiteralSet} that contains no duplicates and unwanted literals. Also checks whether the set contains a literal and its negation.
	 *
	 * @param literalSet The initial literal set.
	 * @param unwantedVariables An array of variables that should be removed.
	 * @return A new literal set or {@code null}, if the initial set contained a literal and its negation.
	 *
	 * @see #cleanLiteralArray(int[], int...)
	 */
	@CheckForNull
	public LiteralSet clean(int... unwantedVariables) {
		final TreeSet<Integer> newLiteralSet = new TreeSet<>();

		for (final int literal : literals) {
			if (newLiteralSet.contains(-literal)) {
				return null;
			} else {
				newLiteralSet.add(literal);
			}
		}

		for (int i = 0; i < unwantedVariables.length; i++) {
			final int unwantedVariable = unwantedVariables[i];
			newLiteralSet.remove(unwantedVariable);
			newLiteralSet.remove(-unwantedVariable);
		}

		final int[] uniqueVarArray = new int[newLiteralSet.size()];
		int i = 0;
		for (final int lit : newLiteralSet) {
			uniqueVarArray[i++] = lit;
		}
		return new LiteralSet(uniqueVarArray, false);
	}

	@Override
	public int hashCode() {
		return hashCode;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}
		return Arrays.equals(literals, ((LiteralSet) obj).literals);
	}

	@Override
	public String toString() {
		return "Clause <" + Arrays.toString(literals) + ">";
	}

	@Override
	public LiteralSet clone() {
		return new LiteralSet(this);
	}

	public boolean isEmpty() {
		return literals.length == 0;
	}

	@Override
	public int compareTo(LiteralSet o) {
		// TODO implement more efficient comparison
		return Arrays.toString(literals).compareTo(Arrays.toString(o.literals));
	}

	public LiteralSet reorder(IVariables oldVariables, IVariables newVariables) {
		final int[] oldLiterals = literals;
		final int[] newLiterals = new int[oldLiterals.length];
		for (int i = 0; i < oldLiterals.length; i++) {
			final int l = oldLiterals[i];
			newLiterals[i] = newVariables.getVariable(oldVariables.getName(l), l > 0);
		}
		return new LiteralSet(newLiterals);
	}

}
