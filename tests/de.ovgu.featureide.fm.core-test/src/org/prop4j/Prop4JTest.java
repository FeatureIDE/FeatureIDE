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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.HashSet;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import junit.framework.JUnit4TestAdapter;

/**
 * Tests for tautologies, node transformations, and node parsing
 *
 * @author Thomas Thuem
 */
public class Prop4JTest {

	private static final long TIMEOUT = 1000;
	private final Literal a = new Literal("a");
	private final Literal b = new Literal("b");
	private final Literal c = new Literal("c");
	private final Literal d = new Literal("d");
	private final Literal e = new Literal("e");
	private final Literal f = new Literal("f");
	private final Literal g = new Literal("g");

	public static junit.framework.Test suite() {
		return new JUnit4TestAdapter(Prop4JTest.class);
	}

	@Test
	public void testTautology1() throws TimeoutException {
		taut(new Not(new Not("p1")), "p1");
	}

	@Test
	public void testTautology2() throws TimeoutException {
		taut(new And("p1", "p1"), "p1");
	}

	@Test
	public void testTautology3() throws TimeoutException {
		taut(new Or("p1", "p1"), "p1");
	}

	@Test
	public void testTautology4() throws TimeoutException {
		taut(new And("p1", "p2"), new And("p2", "p1"));
	}

	@Test
	public void testTautology5() throws TimeoutException {
		taut(new Or("p1", "p2"), new Or(new Literal("p2"), "p1"));
	}

	@Test
	public void testTautology6() throws TimeoutException {
		taut(new Equals("p1", "p2"), new Equals("p2", "p1"));
	}

	@Test
	public void testTautology7() throws TimeoutException {
		taut(new And(new And("p1", "p2"), "p3"), new And("p1", new And("p2", "p3")));
	}

	@Test
	public void testTautology8() throws TimeoutException {
		taut(new Or(new Or("p1", "p2"), "p3"), new Or("p1", new Or("p2", "p3")));
	}

	@Test
	public void testTautology9() throws TimeoutException {
		taut(new Or(new And("p1", "p2"), "p3"), new And(new Or("p1", "p3"), new Or("p2", "p3")));
	}

	@Test
	public void testTautology10() throws TimeoutException {
		taut(new And(new Or("p1", "p2"), "p3"), new Or(new And("p1", "p3"), new And("p2", "p3")));
	}

	@Test
	public void testTautology11() throws TimeoutException {
		taut(new And("p1", "p2"), new Not(new Or(new Not("p1"), new Not("p2"))));
	}

	@Test
	public void testTautology12() throws TimeoutException {
		taut(new Implies("p1", "p2"), new Implies(new Not("p2"), new Not("p1")));
	}

	@Test
	public void testTautology13() throws TimeoutException {
		taut(new Equals("p1", "p2"), new And(new Implies("p1", "p2"), new Implies("p2", "p1")));
	}

	@Test
	public void testTautology14() throws TimeoutException {
		taut(new Implies(new And("p1", new Implies("p1", "p2")), "p2"));
	}

	@Test
	public void testTautology15() throws TimeoutException {
		taut(new Implies(new And(new Implies("p1", "p2"), new Implies("p2", "p3")), new Implies("p1", "p3")));
	}

	@Test
	public void testTautology16() throws TimeoutException {
		taut(new Choose(2, "p1", "p2", "p3"), new And(new Or("p1", "p2"), new Or("p1", "p3"), new Or("p2", "p3"), new Not(new And("p1", "p2", "p3"))));
	}

	@Test
	public void testTautologyImplies() throws TimeoutException {
		taut(new Implies(new And("A", new And(new Or(new Not("A"), new Or("B", "C")), "D")),
				new And("A", new And(new Or(new Not("A"), new Or("B", "C")), "D"))));
	}

	@Test
	public void testDelphi() throws TimeoutException {
		final Node delphi1 = new Implies(new Not("M"), new And("L", "R"));
		final Node delphi2 = new Implies(new Not(new And("L", "M")), new Not("R"));
		final Node delphi3 = new Implies(new Or("L", "R"), new Not("M"));
		final Node delphi = new And(delphi1, delphi2, delphi3);
		final Node solution = new And(new Not("L"), "M", new Not("R"));
		taut(delphi, solution);
	}

	protected void taut(Object node1, Object node2) throws TimeoutException {
		taut(new Equals(node1, node2));
	}

	protected void taut(Node node) throws TimeoutException {
		assertTrue(isTautology(node));
	}

	protected boolean isTautology(Node node) throws TimeoutException {
		return !new SatSolver(new Not(node), TIMEOUT).isSatisfiable();
	}

	@Test
	public void testSolutionCounting1() {
		solutions(2, new And("A", new Not("B"), new Or("A", new Not("C"))));
	}

	@Test
	public void testSolutionCounting2() {
		solutions(3, new Choose(2, "p1", "p2", "p3"));
	}

	@Test
	public void testSolutionCounting3() {
		solutions(3 + 3 + 1, new AtLeast(1, "p1", "p2", "p3"));
	}

	private void solutions(int count, Node node) {
		assertEquals(count, new SatSolver(node, TIMEOUT).countSolutions());
	}

	@Test
	public void testArrayIndexOutOfBounds1() throws TimeoutException {
		Node a = new And(new Literal("A"), new Equals("A", "B"), new Literal("D", false));
		Node b = new And(new Literal("C"), new Equals("C", "D"), new Literal("B", false));
		a = a.clone().toCNF();
		b = b.clone().toCNF();
		final SatSolver solver = new SatSolver(a, TIMEOUT);
		for (Node child : b.getChildren()) {
			if (!(child instanceof Or)) {
				child = new Or(child);
			}
			final Node[] list = Node.clone(child.getChildren());
			for (final Node node : list) {
				((Literal) node).positive ^= true;
			}
			solver.isSatisfiable(list);
		}
	}

// commented out due to false usage of newVar method
//	@Test
//	public void testArrayIndexOutOfBounds2() throws ContradictionException,
//			TimeoutException {
//		ISolver solver = SolverFactory.newDefault();
//		solver.newVar(3);
//		solver.addClause(new VecInt(new int[] { 1 }));
//		solver.addClause(new VecInt(new int[] { -1, 2 }));
//		solver.addClause(new VecInt(new int[] { 1, -2 }));
//		solver.addClause(new VecInt(new int[] { -3 }));
//		solver.newVar(1);
//		solver.isSatisfiable(new VecInt(new int[] { -4 }));
//	}

	@Test
	public void testArrayIndexOutOfBounds3() throws ContradictionException, TimeoutException {
		final ISolver solver = SolverFactory.newDefault();
		solver.newVar(3);
		solver.addClause(new VecInt(new int[] { 1 }));
		solver.addClause(new VecInt(new int[] { -1, 2 }));
		solver.addClause(new VecInt(new int[] { 1, -2 }));
		solver.addClause(new VecInt(new int[] { -3 }));
		solver.newVar(1);
		solver.addClause(new VecInt(new int[] { 4, -4 }));
		solver.isSatisfiable(new VecInt(new int[] { -4 }));
	}

	@Test
	public void testBinom() {
		for (int n = 1; n < 10; n++) {
			assertEquals(1, Node.binom(n, 0));
			assertEquals(n, Node.binom(n, 1));
			assertEquals(n, Node.binom(n, n - 1));
			assertEquals(1, Node.binom(n, n));
			for (int k = 0; k <= n; k++) {
				assertEquals(k * Node.binom(n, k), n * Node.binom(n - 1, k - 1));
				assertEquals(Node.binom(n + 1, k + 1), Node.binom(n, k) + Node.binom(n, k + 1));
				assertEquals(Node.binom(n, k), Node.binom(n, n - k));
			}
		}
	}

	@Test
	public void testChoose() {
		solutions(0, new Choose(-1, "p1", "p2", "p3", "p4"));
		solutions(1, new Choose(0, "p1", "p2", "p3", "p4"));
		solutions(4, new Choose(1, "p1", "p2", "p3", "p4"));
		solutions(6, new Choose(2, "p1", "p2", "p3", "p4"));
		solutions(4, new Choose(3, "p1", "p2", "p3", "p4"));
		solutions(1, new Choose(4, "p1", "p2", "p3", "p4"));
		solutions(0, new Choose(5, "p1", "p2", "p3", "p4"));
	}

	private void testReaderByObject(String constraint, Node cNode) {
		final Node node = new NodeReader().stringToNode(constraint);

		assertEquals(cNode, node);
	}

	@Test
	public void testReaderLiteral() {
		final String testString = "a";

		testReaderByObject(testString, a);
	}

	@Test
	public void testReaderLiteralWithBrackets() {
		final String testString = "((a))";

		testReaderByObject(testString, a);
	}

	@Test
	public void testReaderNot() {
		final String testString = "not a";

		final Node node = new Not(a);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderAnd() {
		final String testString = "a and b";

		final Node node = new And(a, b);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderOr() {
		final String testString = "a or b";

		final Node node = new Or(a, b);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderImplies() {
		final String testString = "a implies b";

		final Node node = new Implies(a, b);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderIff() {
		final String testString = "a iff b";

		final Node node = new Equals(a, b);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithoutBrackets1() {
		final String testString = "a and b or c implies d";

		final Node node = new Implies(new Or(new And(a, b), c), d);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithoutBrackets2() {
		final String testString = "a and not b or c implies d";

		final Node node = new Implies(new Or(new And(a, new Not(b)), c), d);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithoutBrackets3() {
		final String testString = "a iff b or c iff d";

		final Node node = new Equals(a, new Equals(new Or(b, c), d));
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBrackets1() {
		final String testString = "(a implies b) and d";

		final Node node = new And(new Implies(a, b), d);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBrackets2() {
		final String testString = "a and not (b or c implies d)";

		final Node node = new And(a, new Not(new Implies(new Or(b, c), d)));
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBrackets3() {
		final String testString = "(a iff b) or (c iff d)";

		final Node node = new Or(new Equals(a, b), new Equals(c, d));
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBracketsAndSpaces1() {
		final String testString = "( a and b ) or c";

		final Node node = new Or(new And(a, b), c);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBracketsAndSpaces2() {
		final String testString = "(    a iff   b ) or (c iff d)  ";

		final Node node = new Or(new Equals(a, b), new Equals(c, d));
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBrackets5() {
		final String testString = "(a iff b) or (c implies (d) and e or (f iff g))";

		final Node node = new Or(new Equals(a, b), new Implies(c, new Or(new And(d, e), new Equals(f, g))));
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBrackets6() {
		/*
		 * Node node = NodeReader.stringToNode("(((a or b)))"); assetEquals(NodeWriter.node.getChildren()[0]) }
		 */

	}

	@Test
	public void testReaderFeatureNameContainsOperator() {
		final String testString = "Handy";

		final Node node = new Literal("Handy");
		testReaderByObject(testString, node);

	}

	@Test
	public void testReaderEmptyString() {
		new NodeReader().stringToNode("");
		assertTrue(true);
	}

	@Test
	public void testValidatorWithFeatureNames1() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "Hello";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames2() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "(Hello)";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames3() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "affe";

		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));

		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames4() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "and";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames5() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "Hello and";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames6() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "not Hello and World";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames7() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "not Hello and World ()";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames8() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "(Hello))";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames9() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "((not (Hello) and World";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));

	}

	@Test
	public void testValidatorWithFeatureNames10() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "Hello and or";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));

	}

	@Test
	public void testValidatorWithFeatureNames11() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));

	}

	@Test
	public void testValidatorWithFeatureNames12() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = " ";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));

	}

	@Test
	public void testValidatorWithFeatureNames13() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "Hello) or (";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));

	}

	@Test
	public void testValidatorWithFeatureNames14() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "()()()()";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames15() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "Hello Wonderful";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));

	}

	@Test
	public void testValidatorWithFeatureNames16() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		final String constraint = "(World and Beautiful)";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));

	}

	@Test
	public void testValidatorWithFeatureNames17() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful", "Hello and World" };
		final String constraint = "\"Hello and World\" or Wonderful";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames18() {
		final String[] featureNames = { "Beautiful", "Wonderful", "Hello and World" };
		final String constraint = "\"Hello and World\" or Wonderful";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames19() {
		final String[] featureNames = { "Wonderful" };
		final String constraint = "\"Hello and World\" or Wonderful";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames21() {
		final String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful", "Hello and World" };
		final String constraint = "(\"Hello and World\" or Wonderful) or \"Hello\"";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames22() {
		final String[] featureNames = { "Beautiful", "Wonderful", "Hello and World" };
		final String constraint = "(Hello \"and World\" or Wonderful)";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames23() {
		final String[] featureNames = { "Beautiful", "Wonderful", "Hello and World" };
		final String constraint = "((\"Hello and World\") or Wonderful)";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames24() {
		final String[] featureNames = { "Beautiful", "Wonderful", "Hello and World" };
		final String constraint = "((\"Hello and World\") \"or\" Wonderful)";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames25() {
		final String[] featureNames = { "Beautiful and", "Wonderful", "Hello and World" };
		final String constraint = "((((\"Hello and World\" and \"Beautiful and\"))) or Wonderful)";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames26() {
		final String[] featureNames = { "Beautiful and", "Wonderful", "Hello and World" };
		final String constraint = "(((\"Hello and World\" and \"Beautiful and\"))) or Wonderful)";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames27() {
		final String[] featureNames = { "Hello and World" };
		final String constraint = "((((\"Hello and World\" and \"Beautiful and\"))) or Wonderful)";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	private boolean testValidatorWithFeatureNames(String constraint, String[] featureNames) {
		return new NodeReader().isWellFormed(constraint, new HashSet<>(Arrays.asList(featureNames)));
	}

	private boolean testValidatorWithoutFeatureNames(String constraint) {
		return new NodeReader().isWellFormed(constraint);
	}

	@Test
	public void testSimplify1() {
		final Node node = new Or(a, new Or(new Or(b, c), new Or(d, e)));
		node.simplify();

		assertEquals(a, node.getChildren()[0]);
		assertEquals(b, node.getChildren()[1]);
		assertEquals(c, node.getChildren()[2]);
		assertEquals(d, node.getChildren()[3]);
		assertEquals(e, node.getChildren()[4]);
	}

	@Test
	public void testSimplify2() {
		final Node node = new And(a, new And(new And(b, c), new And(d, e)));
		node.simplify();

		assertEquals(a, node.getChildren()[0]);
		assertEquals(b, node.getChildren()[1]);
		assertEquals(c, node.getChildren()[2]);
		assertEquals(d, node.getChildren()[3]);
		assertEquals(e, node.getChildren()[4]);
	}

	@Test
	public void testSimplify3() {
		final Node x = new And(b, c);
		final Node y = new And(d, e);
		final Node node = new Or(a, new Or(x, y));
		node.simplify();

		assertEquals(a, node.getChildren()[0]);
		assertEquals(x, node.getChildren()[1]);
		assertEquals(y, node.getChildren()[2]);
	}

	@Test
	public void testSimplify4() {
		final Node x = new Or(b, c);
		final Node y = new Or(d, e);
		final Node node = new And(a, new And(x, y));
		node.simplify();

		assertEquals(a, node.getChildren()[0]);
		assertEquals(x, node.getChildren()[1]);
		assertEquals(y, node.getChildren()[2]);
	}

	@Test
	public void testSat4J() throws ContradictionException, TimeoutException {
		final ISolver solver = SolverFactory.newDefault();
		solver.setTimeout(15);
		solver.addClause(new VecInt(new int[] { 1 }));
		solver.addClause(new VecInt(new int[] { -1, 2, 3 }));
		solver.addClause(new VecInt(new int[] { 4 }));
		solver.isSatisfiable(new VecInt(new int[] { 1, -2, -3 }));
		assertFalse(solver.isSatisfiable(new VecInt(new int[] { -4 })));

	}

	@Test
	public void problemAymericHervieu() {
		final String ctr = "(C => A) & (E => C) & (G => C) & (D => A) & (F => C) & (C => A) & "
			+ "(I => D) & (B => A) & (D => A) & (J => D) & (J => D) & (B => A) & (E " + "=> C) & (F => C) & (I => D) & (G => C) & A & (False | A) & (A => B) & "
			+ "(C => E | F | G) & (E => -G) & (E => -F) & (F => -G) & (D => J | I) & " + "(I => E)";

		final NodeReader nd = new NodeReader();
		nd.activateShortSymbols();
		assertTrue(nd.isWellFormed(ctr));
		final Node n = nd.stringToNode(ctr);
		assertNotNull(n.getChildren());
	}
}
