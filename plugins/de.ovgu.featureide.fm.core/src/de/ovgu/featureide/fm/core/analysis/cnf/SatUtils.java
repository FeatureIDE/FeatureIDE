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
import java.util.HashSet;

import javax.annotation.CheckForNull;

/**
 *
 * @author Sebastian Krieter
 */
public class SatUtils {

	public static int[] negateSolution(int[] solution) {
		final int[] negSolution = Arrays.copyOf(solution, solution.length);
		for (int i = 0; i < solution.length; i++) {
			negSolution[i] = -solution[i];
		}
		return negSolution;
	}

	public static void updateSolution(final int[] solution1, int[] solution2) {
		for (int i = 0; i < solution1.length; i++) {
			final int x = solution1[i];
			final int y = solution2[i];
			if (x != y) {
				solution1[i] = 0;
			}
		}
	}

	public static void updateSolution(final int[] solution1, Iterable<int[]> solutions) {
		for (int i = 0; i < solution1.length; i++) {
			final int x = solution1[i];
			for (final int[] solution2 : solutions) {
				final int y = solution2[i];
				if (x != y) {
					solution1[i] = 0;
					break;
				}
			}
		}
	}

	public static String toBinaryString(int[] solution) {
		final StringBuilder sb = new StringBuilder(solution.length);
		for (final int literal : solution) {
			sb.append(literal == 0 ? '?' : literal < 0 ? '0' : '1');
		}
		return sb.toString();
	}

	public static int countNegative(int[] solution) {
		int count = 0;
		for (int i = 0; i < solution.length; i++) {
			count += solution[i] >>> (Integer.SIZE - 1);
		}
		return count;
	}

	public static int[] cleanLiteralArray(int[] newLiterals, byte[] helper) {
		int uniqueVarCount = newLiterals.length;
		for (int i = 0; i < newLiterals.length; i++) {
			final int literal = newLiterals[i];

			final int index = Math.abs(literal);
			final byte signum = (byte) Math.signum(literal);

			final int h = helper[index];
			switch (h) {
			case 0:
				helper[index] = signum;
				break;
			case 2:
				helper[index] = signum;
				break;
			case -1:
			case 1:
				if (h == signum) {
					newLiterals[i] = 0;
					uniqueVarCount--;
					break;
				} else {
					// reset
					for (int j = 0; j < i; j++) {
						helper[Math.abs(newLiterals[j])] = 0;
					}
					return null;
				}
			default:
				assert false;
				break;
			}
		}
		if (uniqueVarCount == newLiterals.length) {
			for (int i = 0; i < newLiterals.length; i++) {
				final int literal = newLiterals[i];
				helper[Math.abs(literal)] = 0;
			}
			return newLiterals;
		} else {
			final int[] uniqueVarArray = new int[uniqueVarCount];
			int k = 0;
			for (int i = 0; i < newLiterals.length; i++) {
				final int literal = newLiterals[i];
				helper[Math.abs(literal)] = 0;
				if (literal != 0) {
					uniqueVarArray[k++] = literal;
				}
			}
			return uniqueVarArray;
		}
	}

	/**
	 * Constructs a new array of literals that contains no duplicates and unwanted literals. Also checks whether the array contains a literal and its negation.
	 *
	 * @param literalArray The initial literal array.
	 * @param unwantedVariables An array of variables that should be removed.
	 * @return A new literal array or {@code null}, if the initial set contained a literal and its negation.
	 *
	 * @see #cleanLiteralSet(LiteralSet, int...)
	 */
	@CheckForNull
	public static int[] cleanLiteralArray(int[] literalArray, int... unwantedVariables) {
		final HashSet<Integer> newLiteralSet = new HashSet<>(literalArray.length << 1);

		outer: for (final int literal : literalArray) {
			for (int i = 0; i < unwantedVariables.length; i++) {
				if (unwantedVariables[i] == Math.abs(literal)) {
					continue outer;
				}
			}
			if (newLiteralSet.contains(-literal)) {
				return null;
			} else {
				newLiteralSet.add(literal);
			}
		}

		final int[] uniqueVarArray = new int[newLiteralSet.size()];
		int i = 0;
		for (final int lit : newLiteralSet) {
			uniqueVarArray[i++] = lit;
		}
		return uniqueVarArray;
	}

}
