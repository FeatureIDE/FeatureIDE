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
package org.prop4j.explain.solvers;

import static org.junit.Assert.assertTrue;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.prop4j.And;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISolver;
import org.prop4j.solver.SatResult;

/**
 * Tests for {@link ISolver}.
 *
 * @author Timo G&uuml;nther
 */
public abstract class ISolverTests {

	protected abstract ISolver getInstance(Node cnf);

	@Test
	public void testSatisfiable() {
		final ISolver solver = getInstance(new And(new Literal("A"), new Implies(new Literal("A"), new Literal("B"))));
		assertTrue(solver.isSatisfiable() == SatResult.TRUE);
	}

	@Test
	public void testSatisfiableContradiction() {
		final ISolver solver = getInstance(new And("A", new Not("A")));
		assertTrue(solver.isSatisfiable() == SatResult.FALSE);
	}

	@Test
	public void testSatisfiableUnsatisfiable() {
		final ISolver solver = getInstance(new And("A", new Implies("A", "B"), new Not("B")));
		assertTrue(solver.isSatisfiable() == SatResult.FALSE);
	}

	@Test
	public void testSatisfiableEmpty() {
		final ISolver solver = getInstance(null);
		assertTrue(solver.isSatisfiable() == SatResult.TRUE);
	}

	@Test
	public void testSatisfiableMultiple() {
		final ISolver solver = getInstance(new And("A", new Implies("A", "B")));
		assertTrue(solver.isSatisfiable() == SatResult.TRUE);
		assertTrue(solver.isSatisfiable() == SatResult.TRUE);
		assertTrue(solver.isSatisfiable() == SatResult.TRUE);
	}

	@Test
	public void testSatisfiableIncremental() throws ContradictionException {
		final ISolver solver = getInstance(new And(new Or("A", "B")));
		assertTrue(solver.isSatisfiable() == SatResult.TRUE);
		solver.push(new Or("A", new Not("A")).toRegularCNF());
		assertTrue(solver.isSatisfiable() == SatResult.TRUE);
		solver.push(new Equals("A", "B").toRegularCNF().getChildren());
		assertTrue(solver.isSatisfiable() == SatResult.TRUE);
		solver.push(new Or(new Not("A"), new Not("B")).toRegularCNF());
		assertTrue(solver.isSatisfiable() == SatResult.FALSE);
		solver.push(new Or("B", new Not("B")).toRegularCNF());
		assertTrue(solver.isSatisfiable() == SatResult.FALSE);
	}

	@Test
	public void testSatisfiableAssumptions() throws ContradictionException {
		final ISolver solver = getInstance(new And("A", new Implies("A", "B")));
		assertTrue(solver.isSatisfiable() == SatResult.TRUE);
		solver.push(new Literal("B", true));
		assertTrue(solver.isSatisfiable() == SatResult.TRUE);
		solver.pop();
		solver.push(new Literal("B", false));
		assertTrue(solver.isSatisfiable() == SatResult.FALSE);
		solver.pop();
		solver.push(new Literal("B", true));
		assertTrue(solver.isSatisfiable() == SatResult.TRUE);
		solver.push(new Literal("A", false));
		assertTrue(solver.isSatisfiable() == SatResult.FALSE);
	}

	@Test
	public void testModel() {
		final ISolver solver = getInstance(new And("A", new Not("B")));
		final Object[] actual = solver.findSolution();
		assertTrue((int) actual[0] == 1);
		assertTrue((int) actual[1] == -2);
	}

	@Test
	public void testModelContradiction() {
		final ISolver solver = getInstance(new And("A", new Not("A")));
		final Object[] solution = solver.findSolution();
		assertTrue(solution == null);
	}

	@Test
	public void testModelEmpty() {
		final ISolver solver = getInstance(null);
		final Object[] actual = solver.findSolution();
		assertTrue(actual.length == 0);
	}

	@Test
	public void testModelMultiple() {
		final ISolver solver = getInstance(new And("A", new Not("B")));
		Object[] expected = solver.findSolution();
		assertTrue((int) expected[0] == 1);
		assertTrue((int) expected[1] == -2);
		expected = solver.findSolution();
		assertTrue((int) expected[0] == 1);
		assertTrue((int) expected[1] == -2);
		expected = solver.findSolution();
		assertTrue((int) expected[0] == 1);
		assertTrue((int) expected[1] == -2);
		expected = solver.findSolution();
		assertTrue((int) expected[0] == 1);
		assertTrue((int) expected[1] == -2);
		expected = solver.findSolution();
		assertTrue((int) expected[0] == 1);
		assertTrue((int) expected[1] == -2);
	}

	@Test
	public void testModelAssumptions() throws ContradictionException {
		final ISolver solver = getInstance(new Implies("A", "B").toRegularCNF());
		solver.push(new Literal("B", false));
		final Object[] result = solver.findSolution();
		assertTrue((int) result[0] == -1);
		assertTrue((int) result[1] == -2);

		solver.pop();
		solver.push(new Not("B").toRegularCNF());
		final Object[] result2 = solver.findSolution();
		assertTrue((int) result2[0] == -1);
		assertTrue((int) result2[1] == -2);
	}

	@Rule
	public final ExpectedException exception = ExpectedException.none();

}
