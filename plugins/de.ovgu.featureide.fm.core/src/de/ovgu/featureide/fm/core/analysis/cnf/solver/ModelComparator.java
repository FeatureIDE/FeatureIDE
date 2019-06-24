package de.ovgu.featureide.fm.core.analysis.cnf.solver;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;

public abstract class ModelComparator {

	public static boolean eq(CNF satInstance1, final CNF satInstance2) throws TimeoutException {
		return compare(satInstance2, satInstance1) && compare(satInstance1, satInstance2);
	}

	public static boolean compare(CNF satInstance1, final CNF satInstance2) throws TimeoutException {
		final SimpleSatSolver solver = new SimpleSatSolver(satInstance1);
		for (final LiteralSet clause : satInstance2.getClauses()) {
			final SatResult satResult = solver.hasSolution(clause.negate());
			switch (satResult) {
			case FALSE:
				break;
			case TIMEOUT:
				throw new TimeoutException();
			case TRUE:
				return false;
			default:
				assert false;
			}
		}
		return true;
	}

}
