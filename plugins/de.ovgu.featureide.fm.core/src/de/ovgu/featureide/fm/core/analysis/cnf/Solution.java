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

import java.util.Arrays;

/**
 * A complete list of literals representing a solution to a formula.
 *
 * @author Sebastian Krieter
 */
public class Solution extends LiteralSet {

	private static final long serialVersionUID = -3058742332393418632L;

	public Solution(Solution clause) {
		super(clause);
	}

	public Solution(int... literals) {
		super(literals, false);
	}

	@Override
	protected int getDuplicates(LiteralSet variables, final boolean[] removeMarker) {
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

	@Override
	public int indexOfLiteral(int literal) {
		final int index = Math.abs(literal) - 1;
		return literals[index] == literal ? index : -1;
	}

	@Override
	public int indexOfVariable(int variable) {
		return (variable > 0) && (variable < size()) ? (variable - 1) : -1;
	}

	@Override
	public int countNegative() {
		int count = 0;
		for (final int literal : literals) {
			if (literal < 0) {
				count++;
			}
		}
		return count;
	}

	@Override
	public int countPositive() {
		int count = 0;
		for (final int literal : literals) {
			if (literal > 0) {
				count++;
			}
		}
		return count;
	}

	@Override
	public Solution getVariables() {
		final int[] absoluteLiterals = Arrays.copyOf(literals, literals.length);
		for (int i = 0; i < absoluteLiterals.length; i++) {
			absoluteLiterals[i] = Math.abs(absoluteLiterals[i]);
		}
		return new Solution(absoluteLiterals);
	}

	@Override
	public Solution negate() {
		final int[] negLiterals = Arrays.copyOf(literals, literals.length);
		for (int i = 0; i < negLiterals.length; i++) {
			negLiterals[i] = -literals[i];
		}
		return new Solution(negLiterals);
	}

	@Override
	public String toString() {
		return "Solution [literals=" + Arrays.toString(literals) + "]";
	}

	@Override
	public Solution clone() {
		return new Solution(this);
	}

}
