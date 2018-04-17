/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.sat4j.specs.TimeoutException;

public abstract class ModelComparator {

	public static boolean eq(Node fmNode1, final Node fmNode2) throws TimeoutException {
		return compare(fmNode2, fmNode1) && compare(fmNode1, fmNode2);
	}

	public static boolean compare(Node fmNode1, final Node fmNode2) throws TimeoutException {
		final CNFSolver solver = new CNFSolver(fmNode1);
		try {
			if (fmNode2 instanceof And) {
				for (final Node clause : fmNode2.getChildren()) {
					if (!checkOr(solver, clause)) {
						return false;
					}
				}
			} else {
				return checkOr(solver, fmNode2);
			}
		} catch (final UnkownLiteralException e) {
			return false;
		}
		return true;
	}

	private static boolean checkOr(final CNFSolver solver, Node clause) throws TimeoutException, UnkownLiteralException {
		if (clause instanceof Or) {
			final Node[] clauseChildren = clause.getChildren();
			final Literal[] literals = new Literal[clauseChildren.length];
			for (int k = 0; k < literals.length; k++) {
				final Literal literal = (Literal) clauseChildren[k].clone();
				literal.flip();
				literals[k] = literal;
			}
			if (solver.isSatisfiable(literals)) {
				return false;
			}
		} else {
			return checkLiteral(solver, clause);
		}
		return true;
	}

	private static boolean checkLiteral(final CNFSolver solver, Node clause) throws TimeoutException, UnkownLiteralException {
		final Literal literal = (Literal) clause.clone();
		literal.flip();
		if (solver.isSatisfiable(new Literal[] { literal })) {
			return false;
		}
		return true;
	}

}
