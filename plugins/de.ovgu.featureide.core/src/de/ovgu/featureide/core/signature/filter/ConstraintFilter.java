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
package de.ovgu.featureide.core.signature.filter;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.signature.base.IConstrainedObject;
import de.ovgu.featureide.fm.core.filter.base.IFilter;

public class ConstraintFilter implements IFilter<IConstrainedObject> {

	private final SatSolver solver;

	private final boolean includeNullConstraint;

	public ConstraintFilter(Node... constraints) {
		this(true, constraints);
	}

	public ConstraintFilter(boolean includeNullConstraint, Node... constraints) {
		solver = new SatSolver(new And(constraints), 2000);
		this.includeNullConstraint = includeNullConstraint;
	}

	@Override
	public boolean isValid(IConstrainedObject object) {
		Node constraint = object.getConstraint();

		if (constraint == null) {
			return includeNullConstraint;
		}

		constraint = new Not(constraint).toCNF();

		try {
			if ((constraint instanceof Literal)) {
				return !solver.isSatisfiable(new Node[] { constraint });
			} else if (constraint instanceof Or) {
				return checkOr(constraint);
			} else {
				final Node[] andChildren = constraint.getChildren();
				for (int i = 0; i < andChildren.length; i++) {
					final Node andChild = andChildren[i];
					if (andChild instanceof Or) {
						if (checkOr(andChild)) {
							return true;
						}
					} else {
						if (!solver.isSatisfiable(andChild)) {
							return true;
						}
					}
				}
				return false;
			}
		} catch (final TimeoutException e) {
			CorePlugin.getDefault().logError(e);
			return false;
		}

	}

	private boolean checkOr(Node or) throws TimeoutException {
		for (final Node orChild : or.getChildren()) {
			if (!solver.isSatisfiable(orChild)) {
				return true;
			}
		}
		return false;
	}

}
