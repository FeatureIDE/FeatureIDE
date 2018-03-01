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
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatResult;
import org.prop4j.solver.ISolver;

/**
 * Tests for {@link MutableSatSolver}.
 *
 * @author Timo G&uuml;nther
 */
public abstract class MutableSatSolverTests extends ISolverTests {

	@Test
	public void testPush() throws ContradictionException {
		final ISolver instance = getInstance(new And(new Or("A", new Literal("B", false))));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or("A", new Literal("B", false)));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push(new Or("A", "C"));
		expected.add(new Or("A", "C"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
	}

	@Test
	public void testPushEmpty() throws ContradictionException {
		final ISolver instance = getInstance(null);
		final List<Node> expected = Collections.emptyList();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
	}

	@Test
	public void testPushMultiple() throws ContradictionException {
		final ISolver instance = getInstance(new And(new Or("A", "B")));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or("A", "B"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push(new And(new Or("D", "A"), new Or("B", "D")));
		expected.add(new Or("D", "A"));
		expected.add(new Or("B", "D"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push(new Or("C", "D"));
		expected.add(new Or("C", "D"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push(new Implies("C", "B"));
		expected.add(new Or(new Literal("C", false), "B"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
	}

	@Test
	public void testPop() throws ContradictionException {
		final ISolver instance = getInstance(new And(new Or("A", new Literal("B", false))));
		final Deque<Node> expected = new LinkedList<>();
		expected.add(new Or("A", new Literal("B", false)));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push(new Or("A", "C"));
		expected.add(new Or("A", "C"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.pop();
		expected.removeLast();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
	}
//
//	@Test
//	public void testPopEmpty() {
//		final ISolver instance = getInstance();
//		exception.expect(NoSuchElementException.class);
//		instance.pop();
//	}

	@Test
	public void testPopMultiple() throws ContradictionException {
		final ISolver instance = getInstance(new And(new Or("A", "B")));
		final Deque<Node> expected = new LinkedList<>();
		expected.add(new Or("A", "B"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push(new And(new Or("D"), new Or("B", "D")));
		expected.add(new Or("D"));
		expected.add(new Or("B", "D"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push(new Or("C", "D"));
		expected.add(new Or("C", "D"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.pop();
		expected.removeLast();
		expected.removeLast();
		expected.removeLast();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push(new Implies("C", "B"));
		expected.add(new Or(new Literal("C", false), "B"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.pop();
		expected.removeLast();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		exception.expect(NoSuchElementException.class);
		instance.pop();
	}

	@Test
	public void testPopUnit() throws ContradictionException {
		final ISolver instance = getInstance(new And(new Or("A")));
		final Deque<Node> expected = new LinkedList<>();
		expected.add(new Or("A"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push(new Literal("B", true));
		expected.add(new Or("B"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.pop();
		expected.removeLast();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
	}

	@Test
	public void testPopAssumptions() throws ContradictionException {
		final ISolver instance = getInstance(new And("A", "B"));
		final Deque<Node> expected = new LinkedList<>();
		expected.add(new Or("A"));
		expected.add(new Or("B"));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.push(new Literal("A", false));
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
		instance.pop();
		assertEquals(expected, instance.getClauses());
		assertTrue(instance.isSatisfiable() == ISatResult.TRUE);
	}

	@Override
	protected abstract ISolver getInstance(Node cnf);
}
