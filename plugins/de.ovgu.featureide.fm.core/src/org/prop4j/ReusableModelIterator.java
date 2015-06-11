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
		for (IConstr constraint : constraints) {
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
		if (finished || (max >= 0 && count >= max)) {
			return false;
		}
		try {
			if (assumptions == null) {
				finished = !solver.isSatisfiable(true);
			} else {
				finished = !solver.isSatisfiable(assumptions, true);
			}
		} catch (TimeoutException e) {
			finished = true;
			timeout = true;
		}
		if (finished) {
			return false;
		}
		nextModel = solver.model();
		count++;
		IVecInt clause = new VecInt(nextModel.length);
		for (int q : nextModel) {
			clause.push(-q);
		}
		try {
			constraints.add(solver.addBlockingClause(clause));
		} catch (ContradictionException e) {
			finished = true;
		}
		return true;
	}

	@Override
	public boolean hasNext() {
		return nextModel != null || findNext();
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
	public void remove() {
	}

	public IVecInt getAssumptions() {
		return assumptions;
	}

	public void setAssumptions(IVecInt assumptions) {
		this.assumptions = assumptions;
	}
}
