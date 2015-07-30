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
import java.util.Comparator;

import org.prop4j.Literal;

/**
 * Clause of a CNF.
 * 
 * @author Sebastian Krieter
 */
public class Clause {

	private static final class LiteralComparator implements Comparator<Literal> {
		@Override
		public int compare(Literal arg0, Literal arg1) {
			if (arg0.positive == arg1.positive) {
				return ((String) arg0.var).compareTo((String) arg1.var);
			} else if (arg0.positive) {
				return -1;
			} else {
				return 1;
			}
		}
	}

	private static final LiteralComparator literalComparator = new LiteralComparator();

	protected Literal[] literals;

	public Clause(Literal[] literals) {
		this.literals = literals;
		Arrays.sort(this.literals, literalComparator);
	}

	public Literal[] getLiterals() {
		return literals;
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

}
