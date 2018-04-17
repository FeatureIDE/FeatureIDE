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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import org.junit.Test;
import org.prop4j.And;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Not;
import org.prop4j.Or;

/**
 * Tests for {@link SatSolver}.
 *
 * @author Timo G&uuml;nther
 */
public abstract class SatSolverTests extends SatProblemTests {

	@Test
	public void testSatisfiable() {
		final SatSolver solver = getInstance();
		solver.addFormula(new And("A", new Implies("A", "B")));
		assertTrue(solver.isSatisfiable());
	}

	@Test
	public void testSatisfiableContradiction() {
		final SatSolver solver = getInstance();
		solver.addFormula(new And("A", new Not("A")));
		assertFalse(solver.isSatisfiable());
	}

	@Test
	public void testSatisfiableUnsatisfiable() {
		final SatSolver solver = getInstance();
		solver.addFormula(new And("A", new Implies("A", "B"), new Not("B")));
		assertFalse(solver.isSatisfiable());
	}

	@Test
	public void testSatisfiableEmpty() {
		final SatSolver solver = getInstance();
		assertTrue(solver.isSatisfiable());
	}

	@Test
	public void testSatisfiableMultiple() {
		final SatSolver solver = getInstance();
		solver.addFormula(new And("A", new Implies("A", "B")));
		assertTrue(solver.isSatisfiable());
		assertTrue(solver.isSatisfiable());
		assertTrue(solver.isSatisfiable());
	}

	@Test
	public void testSatisfiableIncremental() {
		final SatSolver solver = getInstance();
		solver.addFormula(new Or("A", "B"));
		assertTrue(solver.isSatisfiable());
		solver.addFormula(new Or("A", new Not("A")));
		assertTrue(solver.isSatisfiable());
		solver.addFormula(new Equals("A", "B"));
		assertTrue(solver.isSatisfiable());
		solver.addFormula(new Or(new Not("A"), new Not("B")));
		assertFalse(solver.isSatisfiable());
		solver.addFormula(new Or("B", new Not("B")));
		assertFalse(solver.isSatisfiable());
	}

	@Test
	public void testSatisfiableAssumptions() {
		final SatSolver solver = getInstance();
		solver.addFormula(new And("A", new Implies("A", "B")));
		assertTrue(solver.isSatisfiable());
		solver.addAssumption("B", true);
		assertTrue(solver.isSatisfiable());
		solver.addAssumption("B", false);
		assertFalse(solver.isSatisfiable());
		solver.addAssumption("B", true);
		assertTrue(solver.isSatisfiable());
		solver.addAssumption("C", false);
		assertTrue(solver.isSatisfiable());
		solver.addAssumption("A", false);
		assertFalse(solver.isSatisfiable());
	}

	@Test
	public void testModel() {
		final SatSolver solver = getInstance();
		solver.addFormula(new And("A", new Not("B")));
		final Map<Object, Boolean> expected = new LinkedHashMap<>();
		expected.put("A", true);
		expected.put("B", false);
		final Map<Object, Boolean> actual = solver.getModel();
		assertEquals(expected, actual);
	}

	@Test
	public void testModelContradiction() {
		final SatSolver solver = getInstance();
		solver.addFormula(new And("A", new Not("A")));
		exception.expect(IllegalStateException.class);
		solver.getModel();
	}

	@Test
	public void testModelUnsatisfiable() {
		final SatSolver solver = getInstance();
		solver.addFormula(new And("A", new Implies("A", "B"), new Not("B")));
		exception.expect(IllegalStateException.class);
		solver.getModel();
	}

	@Test
	public void testModelEmpty() {
		final SatSolver solver = getInstance();
		final Map<Object, Boolean> expected = Collections.emptyMap();
		final Map<Object, Boolean> actual = solver.getModel();
		assertEquals(expected, actual);
	}

	@Test
	public void testModelMultiple() {
		final SatSolver solver = getInstance();
		solver.addFormula(new And("A", new Not("B")));
		final Map<Object, Boolean> expected = new LinkedHashMap<>();
		expected.put("A", true);
		expected.put("B", false);
		assertEquals(expected, solver.getModel());
		assertEquals(expected, solver.getModel());
		assertEquals(expected, solver.getModel());
	}

	@Test
	public void testModelAssumptions() {
		final SatSolver solver = getInstance();
		solver.addFormula(new Implies("A", "B"));
		solver.addAssumption("B", false);
		final Map<Object, Boolean> expected = new LinkedHashMap<>();
		expected.put("A", false);
		expected.put("B", false);
		assertEquals(expected, solver.getModel());
		solver.addAssumption("C", true);
		expected.put("C", true);
		assertEquals(expected, solver.getModel());
	}

	@Override
	protected abstract SatSolver getInstance();
}
