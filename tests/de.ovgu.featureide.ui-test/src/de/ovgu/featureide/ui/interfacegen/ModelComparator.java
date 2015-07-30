package de.ovgu.featureide.ui.interfacegen;

import static org.junit.Assert.fail;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

public abstract class ModelComparator {

	public static boolean eq(Node fmNode1, final Node fmNode2) throws TimeoutException {
		return compare(fmNode2, fmNode1) && compare(fmNode1, fmNode2);
	}

	public static boolean compare(Node fmNode1, final Node fmNode2) throws TimeoutException {
		final SatSolver solver = new SatSolver(fmNode1, 1000);
		if (fmNode2 instanceof And) {
			for (Node clause : fmNode2.getChildren()) {
				if (!checkOr(solver, clause)) {
					return false;
				}
			}
		} else {
			return checkOr(solver, fmNode2);
		}
		return true;
	}

	private static boolean checkOr(final SatSolver solver, Node clause) throws TimeoutException {
		if (clause instanceof Or) {
			Node[] clauseChildren = clause.getChildren();
			Literal[] literals = new Literal[clauseChildren.length];
			for (int k = 0; k < literals.length; k++) {
				final Literal literal = (Literal) clauseChildren[k].clone();
				literal.flip();
				literals[k] = literal;
			}
			if (solver.isSatisfiable(literals)) {
				System.out.println("\nFail!.");
//				fail();
				return false;
			}
		} else {
			return checkLiteral(solver, clause);
		}
		return true;
	}

	private static boolean checkLiteral(final SatSolver solver, Node clause) throws TimeoutException {
		final Literal literal = (Literal) clause.clone();
		literal.flip();
		if (solver.isSatisfiable(new Literal[] { literal })) {
			System.out.println("\nFail!.");
			fail();
			return false;
		}
		return true;
	}

}
