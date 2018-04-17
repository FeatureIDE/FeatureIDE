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
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.prop4j.And;
import org.prop4j.AtLeast;
import org.prop4j.AtMost;
import org.prop4j.Choose;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

/**
 * Tests for {@link SatProblem}.
 *
 * @author Timo G&uuml;nther
 */
public abstract class SatProblemTests {

	@Rule
	public final ExpectedException exception = ExpectedException.none();

	@Test
	public void testAddFormulasVarargs() {
		final SatProblem instance = getInstance();
		instance.addFormulas(new Literal("A", false), new Or("A", "B"));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or(new Literal("A", false)));
		expected.add(new Or("A", "B"));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulasVarargsEmpty() {
		final SatProblem instance = getInstance();
		instance.addFormulas();
		final List<Node> expected = Collections.emptyList();
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulasVarargsNullArray() {
		final SatProblem instance = getInstance();
		final Node[] in = null;
		exception.expect(NullPointerException.class);
		instance.addFormulas(in);
	}

	@Test
	public void testAddFormulasVarargsNullElement() {
		final SatProblem instance = getInstance();
		final Node[] in = new Node[] { null };
		exception.expect(NullPointerException.class);
		instance.addFormulas(in);
	}

	@Test
	public void testAddFormulasCollection() {
		final SatProblem instance = getInstance();
		final Collection<Node> in = Arrays.<Node> asList(new Literal("A", false), new Or("A", "B"));
		instance.addFormulas(in);
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or(new Literal("A", false)));
		expected.add(new Or("A", "B"));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulasCollectionEmpty() {
		final SatProblem instance = getInstance();
		final Collection<Node> in = Collections.emptyList();
		instance.addFormulas(in);
		final List<Node> expected = Collections.emptyList();
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulasCollectionNullArray() {
		final SatProblem instance = getInstance();
		final Collection<Node> in = null;
		exception.expect(NullPointerException.class);
		instance.addFormulas(in);
	}

	@Test
	public void testAddFormulasCollectionNullElement() {
		final SatProblem instance = getInstance();
		final Collection<Node> in = Arrays.asList((Node) null);
		exception.expect(NullPointerException.class);
		instance.addFormulas(in);
	}

	@Test
	public void testAddFormula() {
		final SatProblem instance = getInstance();
		instance.addFormula(new And(new Literal("A", false), new Or("A", "B")));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or(new Literal("A", false)));
		expected.add(new Or("A", "B"));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaEmpty() {
		final SatProblem instance = getInstance();
		instance.addFormula(new And());
		final List<Node> expected = Collections.emptyList();
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaNull() {
		final SatProblem instance = getInstance();
		exception.expect(NullPointerException.class);
		instance.addFormula(null);
	}

	@Test
	public void testAddFormulaMultiple() {
		final SatProblem instance = getInstance();
		instance.addFormula(new And("A", "B"));
		instance.addFormula(new Or("A", "B"));
		instance.addFormula(new And(new Or("B", "A"), new Or("A", "B")));
		instance.addFormula(new Or("B", "C"));
		instance.addFormula(new Literal("C", false));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or("A"));
		expected.add(new Or("B"));
		expected.add(new Or("A", "B"));
		expected.add(new Or("B", "A"));
		expected.add(new Or("A", "B"));
		expected.add(new Or("B", "C"));
		expected.add(new Or(new Literal("C", false)));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaIncremental() {
		final SatProblem instance = getInstance();
		final List<Node> expected = new LinkedList<>();
		instance.addFormula(new And("A", "B"));
		expected.add(new Or("A"));
		expected.add(new Or("B"));
		assertEquals(expected, instance.getClauses());
		instance.addFormula(new Or("A", "B"));
		expected.add(new Or("A", "B"));
		assertEquals(expected, instance.getClauses());
		instance.addFormula(new And(new Or("B", "A"), new Or("A", "B")));
		expected.add(new Or("B", "A"));
		expected.add(new Or("A", "B"));
		assertEquals(expected, instance.getClauses());
		instance.addFormula(new Or("B", "C"));
		expected.add(new Or("B", "C"));
		assertEquals(expected, instance.getClauses());
		instance.addFormula(new Literal("C", false));
		expected.add(new Or(new Literal("C", false)));
		assertEquals(expected, instance.getClauses());
	}

	@Test
	public void testAddFormulaAnd() {
		final SatProblem instance = getInstance();
		instance.addFormula(new And("A", "B"));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or("A"));
		expected.add(new Or("B"));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaOr() {
		final SatProblem instance = getInstance();
		instance.addFormula(new Or("A", "B"));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or("A", "B"));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaNotLiteral() {
		final SatProblem instance = getInstance();
		instance.addFormula(new Literal("A", false));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or(new Literal("A", false)));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaNotNode() {
		final SatProblem instance = getInstance();
		instance.addFormula(new Not("A"));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or(new Literal("A", false)));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaImplies() {
		final SatProblem instance = getInstance();
		instance.addFormula(new Implies("A", "B"));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or(new Literal("A", false), "B"));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaEquals() {
		final SatProblem instance = getInstance();
		instance.addFormula(new Equals("A", "B"));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or(new Literal("A", false), "B"));
		expected.add(new Or(new Literal("B", false), "A"));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaAtLeast() {
		final SatProblem instance = getInstance();
		instance.addFormula(new AtLeast(2, "A", "B", "C"));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or("A", "B"));
		expected.add(new Or("A", "C"));
		expected.add(new Or("B", "C"));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaAtMost() {
		final SatProblem instance = getInstance();
		instance.addFormula(new AtMost(2, "A", "B", "C"));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or(new Literal("A", false), new Literal("B", false), new Literal("C", false)));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaChoose() {
		final SatProblem instance = getInstance();
		instance.addFormula(new Choose(2, "A", "B", "C"));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or(new Literal("A", false), new Literal("B", false), new Literal("C", false)));
		expected.add(new Or("A", "B"));
		expected.add(new Or("A", "C"));
		expected.add(new Or("B", "C"));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaVariablesLetters() {
		final SatProblem instance = getInstance();
		instance.addFormula(new And("A", "B", "C"));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or("A"));
		expected.add(new Or("B"));
		expected.add(new Or("C"));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaVariablesNumbers() {
		final SatProblem instance = getInstance();
		instance.addFormula(new And("1", "2", "-3"));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or("1"));
		expected.add(new Or("2"));
		expected.add(new Or("-3"));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaVariablesIntegers() {
		final SatProblem instance = getInstance();
		instance.addFormula(new And(1, 2, -3));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or(1));
		expected.add(new Or(2));
		expected.add(new Or(-3));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddFormulaVariablesFoo() {
		final SatProblem instance = getInstance();
		instance.addFormula(new And("Foo", "Bar", "Baz"));
		final List<Node> expected = new LinkedList<>();
		expected.add(new Or("Foo"));
		expected.add(new Or("Bar"));
		expected.add(new Or("Baz"));
		final List<Node> actual = instance.getClauses();
		assertEquals(expected, actual);
	}

	@Test
	public void testGetClause() {
		final SatProblem instance = getInstance();
		instance.addFormula(new And("A", new Equals("A", "B"), "C"));
		final Node expected = new Or(new Literal("B", false), "A");
		final Node actual = instance.getClause(2);
		assertEquals(expected, actual);
	}

	@Test
	public void testGetClauseCount() {
		final SatProblem instance = getInstance();
		instance.addFormula(new And("A", new Equals("A", "B"), "C"));
		final int expected = 4;
		final int actual = instance.getClauseCount();
		assertEquals(expected, actual);
	}

	@Test
	public void testAddAssumptions() {
		final SatProblem instance = getInstance();
		final Map<Object, Boolean> expected = new LinkedHashMap<>();
		final Map<Object, Boolean> assumptions = new LinkedHashMap<>();
		assumptions.put("A", true);
		assumptions.put("B", false);
		expected.putAll(assumptions);
		instance.addAssumptions(assumptions);
		assertEquals(expected, instance.getAssumptions());
		assertTrue(instance.getAssumption("A"));
		assertFalse(instance.getAssumption("B"));
		assertNull(instance.getAssumption("C"));
		assumptions.clear();
		assumptions.put("C", false);
		expected.putAll(assumptions);
		instance.addAssumptions(assumptions);
		assertEquals(expected, instance.getAssumptions());
		assertTrue(instance.getAssumption("A"));
		assertFalse(instance.getAssumption("B"));
		assertFalse(instance.getAssumption("C"));
		assumptions.clear();
		assumptions.put("A", false);
		expected.putAll(assumptions);
		instance.addAssumptions(assumptions);
		assertEquals(expected, instance.getAssumptions());
		assertFalse(instance.getAssumption("A"));
		assertFalse(instance.getAssumption("B"));
		assertFalse(instance.getAssumption("C"));
	}

	@Test
	public void testAddAssumption() {
		final SatProblem instance = getInstance();
		final Map<Object, Boolean> expected = new LinkedHashMap<>();
		instance.addAssumption("A", false);
		expected.put("A", false);
		assertEquals(expected, instance.getAssumptions());
		assertFalse(instance.getAssumption("A"));
	}

	protected abstract SatProblem getInstance();
}
