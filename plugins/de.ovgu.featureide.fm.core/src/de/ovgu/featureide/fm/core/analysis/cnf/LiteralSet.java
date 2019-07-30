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
import java.util.Arrays;
import java.util.LinkedHashSet;

import javax.annotation.CheckForNull;

/**
 * A sorted list of literals. Can be used as a clause of a CNF or DNF.
 *
 * @author Sebastian Krieter
 */
public class LiteralSet implements Cloneable, Serializable, Comparable<LiteralSet> {

	public static enum Order {
		NATURAL, INDEX, UNORDERED,
	}

	private static final long serialVersionUID = 8948014814795787431L;

	protected final int[] literals;

	private int hashCode;

	private Order order;

	/**
	 * Constructs a new clause from the given literals. Negates the given literals. <br/> <b>Does not modify the given literal array.</b>
	 *
	 * @param literals literals of the clause
	 * @return A newly constructed clause from the given literals (negated).
	 */
	public static LiteralSet getBlockingClause(int... literals) {
		return new LiteralSet(literals).negate();
	}

	/**
	 * Constructs a new clause from the given literals. <br/> <b>Does not modify the given literal array.</b>
	 *
	 * @param literals literals of the clause
	 * @return A newly constructed clause from the given literals.
	 */
	public static LiteralSet getClause(int... literals) {
		return new LiteralSet(literals);
	}

	/**
	 * Sets the value at position i of solution1 to 0 if the value of solution2 at position i is different.
	 *
	 * @param solution1 First solution.
	 * @param solution2 Second solution.
	 */
	public static void resetConflicts(final int[] solution1, int[] solution2) {
		for (int i = 0; i < solution1.length; i++) {
			final int x = solution1[i];
			final int y = solution2[i];
			if (x != y) {
				solution1[i] = 0;
			}
		}
	}

	/**
	 * Constructs a deep copy of the given clause.
	 *
	 * @param clause the old clause
	 */
	public LiteralSet(LiteralSet clause) {
		literals = Arrays.copyOf(clause.literals, clause.literals.length);
		hashCode = clause.hashCode;
		order = clause.order;
	}

	public LiteralSet(LiteralSet clause, Order literalOrder) {
		literals = Arrays.copyOf(clause.literals, clause.literals.length);
		sortLiterals(literalOrder);
	}

	/**
	 * Constructs a new clause from the given literals. <br/> <b>The resulting clause is backed by the given literal array. The array will be sorted.</b>
	 *
	 * @param literals literals of the clause
	 */
	public LiteralSet(int... literals) {
		this(literals, Order.NATURAL);
	}

	public LiteralSet(int[] literals, Order literalOrder) {
		this(literals, literalOrder, true);
	}

	public LiteralSet(int[] literals, Order literalOrder, boolean sort) {
		this.literals = literals;
		if (sort) {
			sortLiterals(literalOrder);
		} else {
			hashCode = Arrays.hashCode(literals);
			order = literalOrder;
		}
	}

	public void sortLiterals(Order newOrder) {
		switch (newOrder) {
		case INDEX:
			final int[] sortedLiterals = new int[literals.length];
			for (int i = 0; i < literals.length; i++) {
				final int literal = literals[i];
				if (literal != 0) {
					sortedLiterals[Math.abs(literal) - 1] = literal;
				}
			}
			System.arraycopy(sortedLiterals, 0, literals, 0, literals.length);
			break;
		case NATURAL:
			Arrays.sort(literals);
			break;
		case UNORDERED:
			break;
		default:
			break;
		}
		hashCode = Arrays.hashCode(literals);
		order = newOrder;
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
		switch (order) {
		case UNORDERED:
			for (int i = 0; i < literals.length; i++) {
				if (literal == literals[i]) {
					return i;
				}
			}
			return -1;
		case INDEX:
			final int index = Math.abs(literal) - 1;
			return literal == 0 ? -1 : literals[index] == literal ? index : -1;
		case NATURAL:
			return Arrays.binarySearch(literals, literal);
		default:
			throw new AssertionError(order);
		}
	}

	public int indexOfVariable(int variable) {
		switch (order) {
		case INDEX:
			return (variable > 0) && (variable < size()) ? (variable - 1) : -1;
		case UNORDERED:
		case NATURAL:
			for (int i = 0; i < literals.length; i++) {
				if (Math.abs(literals[i]) == variable) {
					return i;
				}
			}
			return -1;
		default:
			throw new AssertionError(order);
		}
	}

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
		switch (order) {
		case UNORDERED:
		case INDEX:
			for (final int literal : literals) {
				if (literal < 0) {
					count++;
				}
			}
			break;
		case NATURAL:
			for (int i = 0; i < literals.length; i++) {
				if (literals[i] < 0) {
					count++;
				} else {
					break;
				}
			}
			break;
		}
		return count;
	}

	public int countPositive() {
		int count = 0;
		switch (order) {
		case UNORDERED:
		case INDEX:
			for (final int literal : literals) {
				if (literal > 0) {
					count++;
				}
			}
			break;
		case NATURAL:
			for (int i = literals.length - 1; i >= 0; i--) {
				if (literals[i] > 0) {
					count++;
				} else {
					break;
				}
			}
			break;
		}
		return count;
	}

	public int size() {
		return literals.length;
	}

	public LiteralSet getVariables() {
		final int[] absoluteLiterals = new int[literals.length];
		for (int i = 0; i < literals.length; i++) {
			absoluteLiterals[i] = Math.abs(literals[i]);
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
		return new LiteralSet(newLiterals, order, false);
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
		return new LiteralSet(newLiterals, order, false);
	}

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
		return hasConflicts(variables.getLiterals());
	}

	public boolean hasConflicts(final int[] otherLiterals) {
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

	/**
	 * Returns a copy of the given array with all entries negated.
	 *
	 * @param solution the given array
	 * @return Array with negated entries.
	 */
	public LiteralSet negate() {
		final int[] negLiterals = new int[literals.length];
		switch (order) {
		case INDEX:
		case UNORDERED:
			for (int i = 0; i < negLiterals.length; i++) {
				negLiterals[i] = -literals[i];
			}
			break;
		case NATURAL:
			final int highestIndex = negLiterals.length - 1;
			for (int i = 0; i < negLiterals.length; i++) {
				negLiterals[highestIndex - i] = -literals[i];
			}
			break;
		}
		return new LiteralSet(negLiterals, order, false);
	}

	public LiteralSet getPositive() {
		final int countPositive = countPositive();
		final int[] positiveLiterals;
		switch (order) {
		case INDEX:
		case UNORDERED:
			positiveLiterals = new int[countPositive];
			int i = 0;
			for (final int literal : literals) {
				if (literal > 0) {
					positiveLiterals[i++] = literal;
				}
			}
			break;
		case NATURAL:
			positiveLiterals = Arrays.copyOfRange(literals, literals.length - countPositive, literals.length);
			break;
		default:
			throw new AssertionError(order);
		}
		return new LiteralSet(positiveLiterals, order, false);
	}

	public LiteralSet getNegative() {
		final int countNegative = countNegative();
		final int[] negativeLiterals;
		switch (order) {
		case INDEX:
		case UNORDERED:
			negativeLiterals = new int[countNegative];
			int i = 0;
			for (final int literal : literals) {
				if (literal < 0) {
					negativeLiterals[i++] = literal;
				}
			}
			break;
		case NATURAL:
			negativeLiterals = Arrays.copyOfRange(literals, 0, countNegative);
			break;
		default:
			throw new AssertionError(order);
		}
		return new LiteralSet(negativeLiterals, order, false);
	}

	/**
	 * Constructs a new {@link LiteralSet} that contains no duplicates and unwanted literals. Also checks whether the set contains a literal and its negation.
	 *
	 * @param literalSet The initial literal set.
	 * @param unwantedVariables An array of variables that should be removed.
	 * @return A new literal set or {@code null}, if the initial set contained a literal and its negation.
	 */
	@CheckForNull
	public LiteralSet clean(int... unwantedVariables) {
		final LinkedHashSet<Integer> newLiteralSet = new LinkedHashSet<>();

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
		return new LiteralSet(uniqueVarArray, order, false);
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
		final int lengthDiff = literals.length - o.literals.length;
		final int length = lengthDiff < 0 ? literals.length : o.literals.length;
		for (int i = 0; i < length; i++) {
			final int diff = literals[i] - o.literals[i];
			if (diff != 0) {
				return diff;
			}
		}
		return lengthDiff;
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

	public String toBinaryString() {
		final StringBuilder sb = new StringBuilder(literals.length);
		for (final int literal : literals) {
			sb.append(literal == 0 ? '?' : literal < 0 ? '0' : '1');
		}
		return sb.toString();
	}

}
