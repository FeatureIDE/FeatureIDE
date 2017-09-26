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
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;

import org.junit.Test;
import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

/**
 * Tests for {@link MutableSatSolver}.
 *
 * @author Timo G&uuml;nther
 */
public abstract class MutableSatSolverTests extends SatSolverTests {

	@Test
	public void testPush() {
		final MutableSatSolver instance = getInstance();
		final List<Node> expected = new LinkedList<>();
		instance.addFormula(new Or("A", new Literal("B", false)));
		expected.add(new Or("A", new Literal("B", false)));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.addFormula(new Or("A", "C"));
		expected.add(new Or("A", "C"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
	}

	@Test
	public void testPushEmpty() {
		final MutableSatSolver instance = getInstance();
		final List<Node> expected = Collections.emptyList();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
	}

	@Test
	public void testPushMultiple() {
		final MutableSatSolver instance = getInstance();
		final List<Node> expected = new LinkedList<>();
		instance.addFormula(new Or("A", "B"));
		expected.add(new Or("A", "B"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.addFormula(new And(new Or("D", "A"), new Or("B", "D")));
		expected.add(new Or("D", "A"));
		expected.add(new Or("B", "D"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.addFormula(new Or("C", "D"));
		expected.add(new Or("C", "D"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.addFormula(new Implies("C", "B"));
		expected.add(new Or(new Literal("C", false), "B"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
	}

	@Test
	public void testPop() {
		final MutableSatSolver instance = getInstance();
		final Deque<Node> expected = new LinkedList<>();
		instance.addFormula(new Or("A", new Literal("B", false)));
		expected.add(new Or("A", new Literal("B", false)));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.addFormula(new Or("A", "C"));
		expected.add(new Or("A", "C"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.pop();
		expected.removeLast();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
	}

	@Test
	public void testPopEmpty() {
		final MutableSatSolver instance = getInstance();
		exception.expect(NoSuchElementException.class);
		instance.pop();
	}

	@Test
	public void testPopMultiple() {
		final MutableSatSolver instance = getInstance();
		final Deque<Node> expected = new LinkedList<>();
		instance.addFormula(new Or("A", "B"));
		expected.add(new Or("A", "B"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.addFormula(new And(new Or("D"), new Or("B", "D")));
		expected.add(new Or("D"));
		expected.add(new Or("B", "D"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.addFormula(new Or("C", "D"));
		expected.add(new Or("C", "D"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.pop();
		expected.removeLast();
		expected.removeLast();
		expected.removeLast();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.addFormula(new Implies("C", "B"));
		expected.add(new Or(new Literal("C", false), "B"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.pop();
		expected.removeLast();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		exception.expect(NoSuchElementException.class);
		instance.pop();
	}

	@Test
	public void testPopUnit() {
		final MutableSatSolver instance = getInstance();
		final Deque<Node> expected = new LinkedList<>();
		instance.addFormula(new Or("A"));
		expected.add(new Or("A"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.addFormula(new Literal("B", true));
		expected.add(new Or("B"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.pop();
		expected.removeLast();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
	}

	@Test
	public void testPopAssumptions() {
		final MutableSatSolver instance = getInstance();
		final Deque<Node> expected = new LinkedList<>();
		instance.addFormula(new And("A", "B"));
		expected.add(new Or("A"));
		expected.add(new Or("B"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
		instance.addAssumption("A", false);
		assertEquals(expected, instance.getClauses());
		assertFalse(instance.isSatisfiable());
		instance.pop();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable());
	}

	@Override
	protected abstract MutableSatSolver getInstance();
}
