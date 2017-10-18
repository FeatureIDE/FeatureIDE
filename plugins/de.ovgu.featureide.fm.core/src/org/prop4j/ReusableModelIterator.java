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
package org.prop4j;

import java.util.ArrayList;
import java.util.Iterator;

import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

public class ReusableModelIterator implements Iterator<int[]> {

	private final ISolver solver;
	private final ArrayList<IConstr> constraints = new ArrayList<>();
	private final long max;

	private long count = 0;
	private boolean timeout = false;
	private IVecInt assumptions = null;

	private int[] nextModel = null;
	private boolean finished = false;

	public ReusableModelIterator(ISolver solver) {
		this(solver, -1);
	}

	public ReusableModelIterator(ISolver solver, long max) {
		this.solver = solver;
		this.max = max;
	}

	public void reset() {
		count = 0;
		assumptions = null;
		timeout = false;
		solver.expireTimeout();
		for (final IConstr constraint : constraints) {
			solver.removeConstr(constraint);
		}
		constraints.clear();
	}

	public long count() {
		while (findNext()) {}
		final long result = timeout ? -count : count;
		reset();
		return result;
	}

	private boolean findNext() {
		if (finished || ((max >= 0) && (count >= max))) {
			return false;
		}
		try {
			if (assumptions == null) {
				finished = !solver.isSatisfiable(true);
			} else {
				finished = !solver.isSatisfiable(assumptions, true);
			}
		} catch (final TimeoutException e) {
			finished = true;
			timeout = true;
		}
		if (finished) {
			return false;
		}
		nextModel = solver.model();
		count++;
		final IVecInt clause = new VecInt(nextModel.length);
		for (final int q : nextModel) {
			clause.push(-q);
		}
		try {
			constraints.add(solver.addBlockingClause(clause));
		} catch (final ContradictionException e) {
			finished = true;
		}
		return true;
	}

	@Override
	public boolean hasNext() {
		return (nextModel != null) || findNext();
	}

	@Override
	public int[] next() {
		if (nextModel == null) {
			findNext();
		}
		final int[] model = nextModel;
		nextModel = null;
		return model;
	}

	@Override
	public void remove() {}

	public IVecInt getAssumptions() {
		return assumptions;
	}

	public void setAssumptions(IVecInt assumptions) {
		this.assumptions = assumptions;
	}
}
