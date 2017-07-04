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
 * Clause of a CNF.
 * 
 * @author Sebastian Krieter
 */
public class LiteralSet implements Cloneable, Serializable {

	private static final long serialVersionUID = 8948014814795787431L;

	protected final int[] literals;

	private final int hashCode;

	public LiteralSet(LiteralSet clause) {
		this.literals = Arrays.copyOf(clause.literals, clause.literals.length);
		hashCode = clause.hashCode;
	}

	public LiteralSet(int... literals) {
		this.literals = literals;
		Arrays.sort(this.literals);

		hashCode = Arrays.hashCode(literals);
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
		return Arrays.binarySearch(literals, literal) >= 0;
	}

	// TODO exploit that both sets are sorted
	public boolean containsAll(LiteralSet otherLiteralSet) {
		for (int otherLiteral : otherLiteralSet.getLiterals()) {
			if (Arrays.binarySearch(literals, otherLiteral) < 0) {
				return false;
			}
		}
		return true;
	}

	public boolean contains(int variable) {
		for (int curLiteral : literals) {
			if (Math.abs(curLiteral) == variable) {
				return true;
			}
		}
		return false;
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
		int[] absoluteLiterals = Arrays.copyOf(literals, literals.length);
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
	private int getDuplicates(LiteralSet variables, final boolean[] removeMarker) {
		final int[] otherLiterals = variables.getLiterals();
		int count = 0;
		for (int i = 0; i < otherLiterals.length; i++) {
			final int otherLiteral = otherLiterals[i];
			for (int j = 0; j < literals.length; j++) {
				if (literals[j] == otherLiteral) {
					count++;
					removeMarker[j] = true;
				}
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
	 * Constructs a new {@link LiteralSet} that contains no duplicates and unwanted literals.
	 * Also checks whether the set contains a literal and its negation.
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

		for (int literal : literals) {
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

		int[] uniqueVarArray = new int[newLiteralSet.size()];
		int i = 0;
		for (int lit : newLiteralSet) {
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
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		return Arrays.equals(literals, ((LiteralSet) obj).literals);
	}

	@Override
	public String toString() {
		return "Clause [literals=" + Arrays.toString(literals) + "]";
	}

	@Override
	public LiteralSet clone() {
		return new LiteralSet(this);
	}

	public boolean isEmpty() {
		return literals.length == 0;
	}

}
