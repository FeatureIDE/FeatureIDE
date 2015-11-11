/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.editing.cnf;

import java.util.Arrays;

/**
 * Clause of a CNF.
 * 
 * @author Sebastian Krieter
 */
public class Clause {

	protected int[] literals;

	public Clause(int... literals) {
		this.literals = literals;
		Arrays.sort(this.literals);
	}

	public int[] getLiterals() {
		return literals;
	}
	
	public boolean contains(int literalID) {
		for (int curLiteralID : literals) {
			if (Math.abs(curLiteralID) == literalID) {
				return true;
			}
		}
		return false;
	}

	@Override
	public int hashCode() {
		return Arrays.hashCode(literals);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		return Arrays.equals(literals, ((Clause) obj).literals);
	}

	@Override
	public String toString() {
		return "Clause [literals=" + Arrays.toString(literals) + "]";
	}

	/**
	 * Checks whether one clause contains the other one or vice-versa.
	 * 
	 * @param clause1 first clause
	 * @param clause2 second clause
	 * 
	 * @return the larger clause (can then be removed from formula)
	 */
	public static Clause contained(Clause clause1, Clause clause2) {
		final int[] literals1 = clause1.literals;
		final int[] literals2 = clause2.literals;
		int index1 = 0;
		int index2 = 0;
		int bigger = 0;

		while (index1 < literals1.length && index2 < literals2.length) {
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
			return literals1.length - literals2.length > 0 ? clause1 : clause2;
		case 1:
			return index2 < literals2.length ? null : clause1;
		case 2:
			return index1 < literals1.length ? null : clause2;
		default:
			return null;
		}
	}

}
