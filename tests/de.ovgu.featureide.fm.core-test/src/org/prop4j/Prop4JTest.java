package org.prop4j;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;

import junit.framework.JUnit4TestAdapter;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

public class Prop4JTest {

	private static final long TIMEOUT = 1000;
	private Literal a = new Literal("a");
	private Literal b = new Literal("b");
	private Literal c = new Literal("c");
	private Literal d = new Literal("d");
	private Literal e = new Literal("e");
	private Literal f = new Literal("f");
	private Literal g = new Literal("g");

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
		taut(new And(new And("p1", "p2"), "p3"), new And("p1", new And("p2",
				"p3")));
	}

	@Test
	public void testTautology8() throws TimeoutException {
		taut(new Or(new Or("p1", "p2"), "p3"), new Or("p1", new Or("p2", "p3")));
	}

	@Test
	public void testTautology9() throws TimeoutException {
		taut(new Or(new And("p1", "p2"), "p3"), new And(new Or("p1", "p3"),
				new Or("p2", "p3")));
	}

	@Test
	public void testTautology10() throws TimeoutException {
		taut(new And(new Or("p1", "p2"), "p3"), new Or(new And("p1", "p3"),
				new And("p2", "p3")));
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
		taut(new Equals("p1", "p2"), new And(new Implies("p1", "p2"),
				new Implies("p2", "p1")));
	}

	@Test
	public void testTautology14() throws TimeoutException {
		taut(new Implies(new And("p1", new Implies("p1", "p2")), "p2"));
	}

	@Test
	public void testTautology15() throws TimeoutException {
		taut(new Implies(new And(new Implies("p1", "p2"), new Implies("p2",
				"p3")), new Implies("p1", "p3")));
	}

	@Test
	public void testTautology16() throws TimeoutException {
		taut(new Choose(2, "p1", "p2", "p3"), new And(new Or("p1", "p2"),
				new Or("p1", "p3"), new Or("p2", "p3"), new Not(new And("p1",
						"p2", "p3"))));
	}

	@Test
	public void testDelphi() throws TimeoutException {
		Node delphi1 = new Implies(new Not("M"), new And("L", "R"));
		Node delphi2 = new Implies(new Not(new And("L", "M")), new Not("R"));
		Node delphi3 = new Implies(new Or("L", "R"), new Not("M"));
		Node delphi = new And(delphi1, delphi2, delphi3);
		Node solution = new And(new Not("L"), "M", new Not("R"));
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
		Node a = new And(new Literal("A"), new Equals("A", "B"), new Literal(
				"D", false));
		Node b = new And(new Literal("C"), new Equals("C", "D"), new Literal(
				"B", false));
		a = a.clone().toCNF();
		b = b.clone().toCNF();
		SatSolver solver = new SatSolver(a, TIMEOUT);
		for (Node child : b.getChildren()) {
			if (!(child instanceof Or))
				child = new Or(child);
			Node[] list = Node.clone(child.getChildren());
			for (Node node : list)
				((Literal) node).positive ^= true;
			solver.isSatisfiable(list);
		}
	}

	@Test
	public void testArrayIndexOutOfBounds2() throws ContradictionException,
			TimeoutException {
		ISolver solver = SolverFactory.newDefault();
		solver.newVar(3);
		solver.addClause(new VecInt(new int[] { 1 }));
		solver.addClause(new VecInt(new int[] { -1, 2 }));
		solver.addClause(new VecInt(new int[] { 1, -2 }));
		solver.addClause(new VecInt(new int[] { -3 }));
		solver.newVar(1);
		try {
			solver.isSatisfiable(new VecInt(new int[] { -4 }));
		} catch (ArrayIndexOutOfBoundsException e) {
			assertTrue(false);
		}
	}

	@Test
	public void testArrayIndexOutOfBounds3() throws ContradictionException,
			TimeoutException {
		ISolver solver = SolverFactory.newDefault();
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
		// show pascal
		// for (int i = 0; i <= 10; i++) {
		// for (int k = 0; k <= i; k++) {
		// System.out.print(Node.binom(i, k) + "   ");
		// }
		// System.out.println();
		// }
		for (int n = 1; n < 10; n++) {
			assertEquals(1, Node.binom(n, 0));
			assertEquals(n, Node.binom(n, 1));
			assertEquals(n, Node.binom(n, n - 1));
			assertEquals(1, Node.binom(n, n));
			for (int k = 0; k <= n; k++) {
				assertEquals(k * Node.binom(n, k), n * Node.binom(n - 1, k - 1));
				assertEquals(Node.binom(n + 1, k + 1),
						Node.binom(n, k) + Node.binom(n, k + 1));
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

	// @Test
	// public void testUsage() {
	// Object[] var = new Object[] {"p1", 2, 3.0, "d"};
	// Node node1 = new Or(var[0], new Equals(var[1], var[2]));
	// Node node2 = new Implies(var[3], new AtLeast(2, var[1], var[2], var[3]));
	// Node node = new And(node1, node2, var[3]);
	// SatSolver solver = new SatSolver(node, 500);
	// try {
	// if (solver.isSatisfiable())
	// System.out.println(solver.getSolutions(5));
	// else
	// System.out.println("No solutions.");
	// } catch (TimeoutException e) {
	// System.out.println("Timeout!");
	// }
	// }

	// @Test
	// public void testExplosion() {
	// LinkedList<Node> children = new LinkedList<Node>();
	// for (int i = 1; i <= 10; i++)
	// children.add(new Literal(i));
	// Node node = new AtMost(1, children);
	// node = node.toCNFprintln();
	// node = new Not(node).toCNFprintln();
	// }

	private void testReaderByObject(String constraint, Node cNode) {


		Node node = new NodeReader().stringToNode(constraint);

		assertEquals(node, cNode);
	}

	@Test
	public void testReaderLiteral() {
		String testString = "a";

		testReaderByObject(testString, a);
	}

	public void testReaderLiteralWithBrackets() {
		String testString = "((a))";

		testReaderByObject(testString, a);
	}

	@Test
	public void testReaderNot() {
		String testString = "not a";

		Node node = new Not(a);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderAnd() {
		String testString = "a and b";

		Node node = new And(a, b);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderOr() {
		String testString = "a or b";

		Node node = new Or(a, b);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderImplies() {
		String testString = "a implies b";

		Node node = new Implies(a, b);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderIff() {
		String testString = "a iff b";

		Node node = new Equals(a, b);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithoutBrackets1() {
		String testString = "a and b or c implies d";

		Node node = new Implies(new Or(new And(a, b), c), d);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithoutBrackets2() {
		String testString = "a and not b or c implies d";

		Node node = new Implies(new Or(new And(a, new Not(b)), c), d);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithoutBrackets3() {
		String testString = "a iff b or c iff d";

		Node node = new Equals(a, new Equals(new Or(b, c), d));
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBrackets1() {
		String testString = "(a implies b) and d";

		Node node = new And(new Implies(a, b), d);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBrackets2() {
		String testString = "a and not (b or c implies d)";

		Node node = new And(a, new Not(new Implies(new Or(b, c), d)));
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBrackets3() {
		String testString = "(a iff b) or (c iff d)";

		Node node = new Or(new Equals(a, b), new Equals(c, d));
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBracketsAndSpaces1() {
		String testString = "( a and b ) or c";

		Node node = new Or(new And(a, b), c);
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBracketsAndSpaces2() {
		String testString = "(    a iff   b ) or (c iff d)  ";

		Node node = new Or(new Equals(a, b), new Equals(c, d));
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBrackets5() {
		String testString = "(a iff b) or (c implies (d) and e or (f iff g))";

		Node node = new Or(new Equals(a, b), new Implies(c, new Or(
				new And(d, e), new Equals(f, g))));
		testReaderByObject(testString, node);
	}

	@Test
	public void testReaderWithBrackets6() {
		/*
		 * Node node = NodeReader.stringToNode("(((a or b)))");
		 * assetEquals(NodeWriter.node.getChildren()[0]) }
		 */

	}
	@Test
	public void testReaderFeatureNameContainsOperator() {
		String testString = "Handy";

		Node node = new Literal("Handy");
		testReaderByObject(testString, node);

	}
	
	@Test
	public void testReaderEmptyString() {
		new NodeReader().stringToNode("");
		assertTrue(true);
	}
	
	@Test
	public void testValidatorWithFeatureNames1() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "Hello";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames2() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "(Hello)";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}



	@Test
	public void testValidatorWithFeatureNames3() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "affe";
	
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));

		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames4() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "and";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames5() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "Hello and";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames6() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "not Hello and World";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));
	}

	@Test
	public void testValidatorWithFeatureNames7() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "not Hello and World ()";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));

	}
	@Test
	public void testValidatorWithFeatureNames8() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "(Hello))";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));
	}
	@Test
	public void testValidatorWithFeatureNames9() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "((not (Hello) and World";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));

	}
	@Test
	public void testValidatorWithFeatureNames10() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "Hello and or";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));

	}
	@Test
	public void testValidatorWithFeatureNames11() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));

	}
	
	@Test
	public void testValidatorWithFeatureNames12() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = " ";
		assertTrue(testValidatorWithFeatureNames(constraint, featureNames));
		assertTrue(testValidatorWithoutFeatureNames(constraint));

	}
	@Test
	public void testValidatorWithFeatureNames13() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "Hello) or (";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));

	}
	@Test
	public void testValidatorWithFeatureNames14() {
		String[] featureNames = { "Hello", "World", "Beautiful", "Wonderful" };
		String constraint = "Hello) or (World";
		assertFalse(testValidatorWithFeatureNames(constraint, featureNames));
		assertFalse(testValidatorWithoutFeatureNames(constraint));

	}
	
	private boolean testValidatorWithFeatureNames(String constraint,
			String[] featureNames) {
			NodeReader n = new NodeReader();
			return n.isWellFormed(constraint,Arrays.asList(featureNames));
	}

	private boolean testValidatorWithoutFeatureNames(String constraint) {
		NodeReader n = new NodeReader();
		return n.isWellFormed(constraint);
	}
	

}