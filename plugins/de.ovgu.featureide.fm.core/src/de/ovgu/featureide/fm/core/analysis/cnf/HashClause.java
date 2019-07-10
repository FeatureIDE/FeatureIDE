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

import java.util.Arrays;

/**
 * Clause of a CNF with special hash value for checking subsumptions.
 *
 * @author Sebastian Krieter
 */
public class HashClause extends LiteralSet {

	private static final long serialVersionUID = 3833046918868446102L;

	private static final int HASHSIZE = 64;

	private final long hashValue;

	public HashClause(int... literals) {
		super(literals);

		int literalHash = 0;
		for (final int literal : literals) {
			literalHash |= (1 << (Math.abs(literal) % HASHSIZE));
		}
		hashValue = literalHash;
	}

	public HashClause(HashClause clause) {
		super(clause);
		hashValue = clause.hashValue;
	}

	/**
	 * Checks whether one clause contains the other one or vice-versa.
	 *
	 * @param clause1 first clause
	 * @param clause2 second clause
	 *
	 * @return the larger clause (can then be removed from formula)
	 */
	public static HashClause contained2(HashClause clause1, HashClause clause2) {
		final int[] literals1 = clause1.literals;
		final int[] literals2 = clause2.literals;
		int index1 = 0;
		int index2 = 0;
		int bigger = 0;

		while ((index1 < literals1.length) && (index2 < literals2.length)) {
			final int diff = literals1[index1] - literals2[index2];
			if (diff < 0) {
				if (bigger == 2) {
					return null;
				}
				bigger = 1;
				index1++;
			} else if (diff > 0) {
				if (bigger == 1) {
					return null;
				}
				bigger = 2;
				index2++;
			} else {
				index1++;
				index2++;
			}
		}

		switch (bigger) {
		case 0:
			return (literals1.length - literals2.length) > 0 ? clause1 : clause2;
		case 1:
			return index2 < literals2.length ? null : clause1;
		case 2:
			return index1 < literals1.length ? null : clause2;
		default:
			return null;
		}
	}

	/**
	 * Checks whether one clause contains the other one or vice-versa.
	 *
	 * @param clause1 first clause
	 * @param clause2 second clause
	 *
	 * @return The larger clause (can then be removed from formula). <br/> If both clauses are equal, the first clause is returned.
	 */
	public static HashClause contained(HashClause clause1, HashClause clause2) {
		final int[] literals1 = clause1.literals;
		final int[] literals2 = clause2.literals;

		if (literals1.length == literals2.length) {
			return ((clause1.hashValue == clause2.hashValue) && Arrays.equals(literals1, literals2)) ? clause1 : null;
		} else {
			final long combinedHash = clause1.hashValue & clause2.hashValue;
			if (literals1.length < literals2.length) {
				if (combinedHash == clause1.hashValue) {
					int index1 = 0;
					int index2 = 0;
					while ((index1 < literals1.length) && (index2 < literals2.length)) {
						final int diff = literals1[index1] - literals2[index2];
						if (diff < 0) {
							return null;
						} else if (diff > 0) {
							index2++;
						} else {
							index1++;
							index2++;
						}
					}

					return index1 < literals1.length ? null : clause2;
				}
			} else {
				if (combinedHash == clause2.hashValue) {
					int index1 = 0;
					int index2 = 0;
					while ((index1 < literals1.length) && (index2 < literals2.length)) {
						final int diff = literals1[index1] - literals2[index2];
						if (diff < 0) {
							index1++;
						} else if (diff > 0) {
							return null;
						} else {
							index1++;
							index2++;
						}
					}

					return index2 < literals2.length ? null : clause1;
				}
			}

		}
		return null;
	}

	public long hashValue() {
		return hashValue;
	}

	@Override
	public HashClause clone() {
		return new HashClause(this);
	}

}
