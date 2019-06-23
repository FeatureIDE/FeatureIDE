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

import static org.junit.Assert.assertFalse;
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
import org.prop4j.solver.ISatResult;
import org.prop4j.solver.ISolver;

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
		assertTrue(solver.isSatisfiable() == ISatResult.TRUE);
	}

	@Test
	public void testSatisfiableContradiction() {
		final ISolver solver = getInstance(new And("A", new Not("A")));
		assertTrue(solver.isSatisfiable() == ISatResult.FALSE);
	}

	@Test
	public void testSatisfiableUnsatisfiable() {
		final ISolver solver = getInstance(new And("A", new Implies("A", "B"), new Not("B")));
		assertTrue(solver.isSatisfiable() == ISatResult.FALSE);
	}

	@Test
	public void testSatisfiableEmpty() {
		final ISolver solver = getInstance(null);
		assertTrue(solver.isSatisfiable() == ISatResult.TRUE);
	}

	@Test
	public void testSatisfiableMultiple() {
		final ISolver solver = getInstance(new And("A", new Implies("A", "B")));
		assertTrue(solver.isSatisfiable() == ISatResult.TRUE);
		assertTrue(solver.isSatisfiable() == ISatResult.TRUE);
		assertTrue(solver.isSatisfiable() == ISatResult.TRUE);
	}

	@Test
	public void testSatisfiableIncremental() throws ContradictionException {
		final ISolver solver = getInstance(new And(new Or("A", "B")));
		assertTrue(solver.isSatisfiable() == ISatResult.TRUE);
		solver.push(new Or("A", new Not("A")));
		assertTrue(solver.isSatisfiable() == ISatResult.TRUE);
		solver.push(new Equals("A", "B").toRegularCNF());
		assertTrue(solver.isSatisfiable() == ISatResult.TRUE);
		solver.push(new Or(new Not("A"), new Not("B")));
		assertFalse(solver.isSatisfiable() == ISatResult.FALSE);
		solver.push(new Or("B", new Not("B")));
		assertFalse(solver.isSatisfiable() == ISatResult.FALSE);
	}

	@Test
	public void testSatisfiableAssumptions() throws ContradictionException {
		final ISolver solver = getInstance(new And("A", new Implies("A", "B")));
		assertTrue(solver.isSatisfiable() == ISatResult.TRUE);
		solver.push(new Literal("B", true));
		assertTrue(solver.isSatisfiable() == ISatResult.TRUE);
		solver.pop();
		solver.push(new Literal("B", false));
		assertTrue(solver.isSatisfiable() == ISatResult.FALSE);
		solver.pop();
		solver.push(new Literal("B", true));
		assertTrue(solver.isSatisfiable() == ISatResult.TRUE);
		solver.push(new Literal("A", false));
		assertTrue(solver.isSatisfiable() == ISatResult.FALSE);
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
		final ISolver solver = getInstance(new Implies("A", "B"));
		solver.push(new Literal("B", false));
		final Object[] result = solver.findSolution();
		assertTrue((int) result[0] == -1);
		assertTrue((int) result[1] == -2);

		solver.pop();
		solver.push(new Not("B"));
		final Object[] result2 = solver.findSolution();
		assertTrue((int) result2[0] == -1);
		assertTrue((int) result2[1] == -2);
	}

	@Rule
	public final ExpectedException exception = ExpectedException.none();

//	@Test
//	public void testpushsVarargs() {
//		final ISolver instance = getInstance(new And(new Or("A", "B")));
//		instance.push(new Literal("A", false));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or(new Literal("A", false)));
//		expected.add(new Or("A", "B"));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}

//	@Test
//	public void testpushsVarargsEmpty() {
//		final ISolver instance = getInstance(null);
//		instance.pushs();
//		final List<Node> expected = Collections.emptyList();
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushsVarargsNullArray() {
//		final ISolver instance = getInstance();
//		final Node[] in = null;
//		exception.expect(NullPointerException.class);
//		instance.pushs(in);
//	}
//
//	@Test
//	public void testpushsVarargsNullElement() {
//		final ISolver instance = getInstance();
//		final Node[] in = new Node[] { null };
//		exception.expect(NullPointerException.class);
//		instance.pushs(in);
//	}
//
//	@Test
//	public void testpushsCollection() {
//		final ISolver instance = getInstance();
//		final Collection<Node> in = Arrays.<Node> asList(new Literal("A", false), new Or("A", "B"));
//		instance.pushs(in);
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or(new Literal("A", false)));
//		expected.add(new Or("A", "B"));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushsCollectionEmpty() {
//		final ISolver instance = getInstance();
//		final Collection<Node> in = Collections.emptyList();
//		instance.pushs(in);
//		final List<Node> expected = Collections.emptyList();
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushsCollectionNullArray() {
//		final ISolver instance = getInstance();
//		final Collection<Node> in = null;
//		exception.expect(NullPointerException.class);
//		instance.pushs(in);
//	}
//
//	@Test
//	public void testpushsCollectionNullElement() {
//		final ISolver instance = getInstance();
//		final Collection<Node> in = Arrays.asList((Node) null);
//		exception.expect(NullPointerException.class);
//		instance.pushs(in);
//	}
//
//	@Test
//	public void testpush() {
//		final ISolver instance = getInstance();
//		instance.push(new And(new Literal("A", false), new Or("A", "B")));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or(new Literal("A", false)));
//		expected.add(new Or("A", "B"));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushEmpty() {
//		final ISolver instance = getInstance();
//		instance.push(new And());
//		final List<Node> expected = Collections.emptyList();
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushNull() {
//		final ISolver instance = getInstance();
//		exception.expect(NullPointerException.class);
//		instance.push(null);
//	}
//
//	@Test
//	public void testpushMultiple() {
//		final ISolver instance = getInstance();
//		instance.push(new And("A", "B"));
//		instance.push(new Or("A", "B"));
//		instance.push(new And(new Or("B", "A"), new Or("A", "B")));
//		instance.push(new Or("B", "C"));
//		instance.push(new Literal("C", false));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or("A"));
//		expected.add(new Or("B"));
//		expected.add(new Or("A", "B"));
//		expected.add(new Or("B", "A"));
//		expected.add(new Or("A", "B"));
//		expected.add(new Or("B", "C"));
//		expected.add(new Or(new Literal("C", false)));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushIncremental() {
//		final ISolver instance = getInstance();
//		final List<Node> expected = new LinkedList<>();
//		instance.push(new And("A", "B"));
//		expected.add(new Or("A"));
//		expected.add(new Or("B"));
//		assertEquals(expected, instance.getClauses());
//		instance.push(new Or("A", "B"));
//		expected.add(new Or("A", "B"));
//		assertEquals(expected, instance.getClauses());
//		instance.push(new And(new Or("B", "A"), new Or("A", "B")));
//		expected.add(new Or("B", "A"));
//		expected.add(new Or("A", "B"));
//		assertEquals(expected, instance.getClauses());
//		instance.push(new Or("B", "C"));
//		expected.add(new Or("B", "C"));
//		assertEquals(expected, instance.getClauses());
//		instance.push(new Literal("C", false));
//		expected.add(new Or(new Literal("C", false)));
//		assertEquals(expected, instance.getClauses());
//	}
//
//	@Test
//	public void testpushAnd() {
//		final ISolver instance = getInstance();
//		instance.push(new And("A", "B"));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or("A"));
//		expected.add(new Or("B"));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushOr() {
//		final ISolver instance = getInstance();
//		instance.push(new Or("A", "B"));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or("A", "B"));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushNotLiteral() {
//		final ISolver instance = getInstance();
//		instance.push(new Literal("A", false));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or(new Literal("A", false)));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushNotNode() {
//		final ISolver instance = getInstance();
//		instance.push(new Not("A"));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or(new Literal("A", false)));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushImplies() {
//		final ISolver instance = getInstance();
//		instance.push(new Implies("A", "B"));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or(new Literal("A", false), "B"));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushEquals() {
//		final ISolver instance = getInstance();
//		instance.push(new Equals("A", "B"));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or(new Literal("A", false), "B"));
//		expected.add(new Or(new Literal("B", false), "A"));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushAtLeast() {
//		final ISolver instance = getInstance();
//		instance.push(new AtLeast(2, "A", "B", "C"));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or("A", "B"));
//		expected.add(new Or("A", "C"));
//		expected.add(new Or("B", "C"));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushAtMost() {
//		final ISolver instance = getInstance();
//		instance.push(new AtMost(2, "A", "B", "C"));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or(new Literal("A", false), new Literal("B", false), new Literal("C", false)));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushChoose() {
//		final ISolver instance = getInstance();
//		instance.push(new Choose(2, "A", "B", "C"));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or(new Literal("A", false), new Literal("B", false), new Literal("C", false)));
//		expected.add(new Or("A", "B"));
//		expected.add(new Or("A", "C"));
//		expected.add(new Or("B", "C"));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushVariablesLetters() {
//		final ISolver instance = getInstance();
//		instance.push(new And("A", "B", "C"));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or("A"));
//		expected.add(new Or("B"));
//		expected.add(new Or("C"));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushVariablesNumbers() {
//		final ISolver instance = getInstance();
//		instance.push(new And("1", "2", "-3"));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or("1"));
//		expected.add(new Or("2"));
//		expected.add(new Or("-3"));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushVariablesIntegers() {
//		final ISolver instance = getInstance();
//		instance.push(new And(1, 2, -3));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or(1));
//		expected.add(new Or(2));
//		expected.add(new Or(-3));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testpushVariablesFoo() {
//		final ISolver instance = getInstance();
//		instance.push(new And("Foo", "Bar", "Baz"));
//		final List<Node> expected = new LinkedList<>();
//		expected.add(new Or("Foo"));
//		expected.add(new Or("Bar"));
//		expected.add(new Or("Baz"));
//		final List<Node> actual = instance.getClauses();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testGetClause() {
//		final ISolver instance = getInstance();
//		instance.push(new And("A", new Equals("A", "B"), "C"));
//		final Node expected = new Or(new Literal("B", false), "A");
//		final Node actual = instance.getClause(2);
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testGetClauseCount() {
//		final ISolver instance = getInstance();
//		instance.push(new And("A", new Equals("A", "B"), "C"));
//		final int expected = 4;
//		final int actual = instance.getClauseCount();
//		assertEquals(expected, actual);
//	}
//
//	@Test
//	public void testAddAssumptions() {
//		final ISolver instance = getInstance();
//		final Map<Object, Boolean> expected = new LinkedHashMap<>();
//		final Map<Object, Boolean> assumptions = new LinkedHashMap<>();
//		assumptions.put("A", true);
//		assumptions.put("B", false);
//		expected.putAll(assumptions);
//		instance.addAssumptions(assumptions);
//		assertEquals(expected, instance.getAssumptions());
//		assertTrue(instance.getAssumption("A"));
//		assertFalse(instance.getAssumption("B"));
//		assertNull(instance.getAssumption("C"));
//		assumptions.clear();
//		assumptions.put("C", false);
//		expected.putAll(assumptions);
//		instance.addAssumptions(assumptions);
//		assertEquals(expected, instance.getAssumptions());
//		assertTrue(instance.getAssumption("A"));
//		assertFalse(instance.getAssumption("B"));
//		assertFalse(instance.getAssumption("C"));
//		assumptions.clear();
//		assumptions.put("A", false);
//		expected.putAll(assumptions);
//		instance.addAssumptions(assumptions);
//		assertEquals(expected, instance.getAssumptions());
//		assertFalse(instance.getAssumption("A"));
//		assertFalse(instance.getAssumption("B"));
//		assertFalse(instance.getAssumption("C"));
//	}
//
//	@Test
//	public void testAddAssumption() {
//		final ISolver instance = getInstance();
//		final Map<Object, Boolean> expected = new LinkedHashMap<>();
//		instance.addAssumption("A", false);
//		expected.put("A", false);
//		assertEquals(expected, instance.getAssumptions());
//		assertFalse(instance.getAssumption("A"));
//	}

}
