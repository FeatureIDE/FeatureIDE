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
package org.prop4j.solvers;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;

import org.junit.Test;
import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.impl.SatProblem;
import org.prop4j.solvers.impl.javasmt.NewProblemSolverMemory;
import org.prop4j.solvers.impl.javasmt.SolverMemory;

/**
 * Test to check the functionality of {@link SolverMemory}
 *
 * @author Joshua Sprey
 */
public class SolverMemoryTest {

	private final SatProblem problem;

	public SolverMemoryTest() {
		final Literal A = new Literal("A");

		final Node cnf = new And(A, new Or(new Literal("B", false), A), new Or(new Literal("C", false), A));
		problem = new SatProblem(cnf.toRegularCNF());
	}

	public NewProblemSolverMemory<Node, Node> getNewEmptyMemory() {
		return new NewProblemSolverMemory<>();
	}

	public NewProblemSolverMemory<Node, Node> getNewFilledMemory() {
		return new NewProblemSolverMemory<>(problem, Arrays.asList(problem.getClauses()));
	}

	@Test
	public void testVariablesEmpty() {
		final NewProblemSolverMemory<Node, Node> memory = getNewEmptyMemory();
		memory.addVariable("A", 1);
		memory.addVariable("B", 5);
		memory.addVariable("C", 10);
		assertTrue(memory.isVariablePresent("A"));
		assertTrue(memory.isVariablePresent("B"));
		assertTrue(memory.isVariablePresent("C"));
		assertEquals(memory.getIndexOfVariable("A"), 1);
		assertEquals(memory.getIndexOfVariable("B"), 5);
		assertEquals(memory.getIndexOfVariable("C"), 10);
		assertEquals(memory.getVariableOfIndex(1), "A");
		assertEquals(memory.getVariableOfIndex(5), "B");
		assertEquals(memory.getVariableOfIndex(10), "C");
	}

	@Test
	public void testVariablesFilled() {
		final NewProblemSolverMemory<Node, Node> memory = getNewFilledMemory();
		assertTrue(memory.isVariablePresent("A"));
		assertTrue(memory.isVariablePresent("B"));
		assertTrue(memory.isVariablePresent("C"));

		memory.addVariable("B", 2);
		memory.addVariable("D", 885);

		assertEquals(memory.getIndexOfVariable("D"), 885);
		assertEquals(memory.getVariableOfIndex(885), "D");
	}

	@Test
	public void testPushPopClauseEmpty() {
		final NewProblemSolverMemory<Node, Node> memory = getNewEmptyMemory();
		final Node testNode = new Or(new Literal("A"), new Literal("B"), new Literal("C"));
		memory.push(testNode, testNode);

		assertEquals(testNode, memory.getClauseOfIndex(0));
		assertEquals(0, memory.getIndexOfClause(testNode));

		final Node node = memory.pop();

		assertEquals(testNode, node);

		memory.push(node, node);

		assertEquals(node, memory.getClauseOfIndex(0));
		assertEquals(0, memory.getIndexOfClause(testNode));
	}

	@Test
	public void testPushPopClauseFilled() {
		final NewProblemSolverMemory<Node, Node> memory = getNewFilledMemory();
		final Node testNode = new Or(new Literal("A"), new Literal("B"), new Literal("C"));
		memory.push(testNode, testNode);

		assertEquals(testNode, memory.getClauseOfIndex(3));
		assertEquals(3, memory.getIndexOfClause(testNode));

		final Node node = memory.pop();

		assertEquals(testNode, node);
		memory.push(node, node);

		assertEquals(node, memory.getClauseOfIndex(3));
		assertEquals(3, memory.getIndexOfClause(testNode));

		memory.pop();

		final Node testNode4 = new Or(new Literal("B"), new Literal("A"), new Literal("C"));
		final Node testNode5 = new Or(new Literal("C", false), new Literal("A"), new Literal("B"));

		memory.push(testNode4, testNode4);
		memory.push(testNode5, testNode5);

		assertEquals(testNode4, memory.getClauseOfIndex(3));
		assertEquals(3, memory.getIndexOfClause(testNode4));
		assertEquals(testNode5, memory.getClauseOfIndex(4));
		assertEquals(4, memory.getIndexOfClause(testNode5));

		memory.push(testNode, testNode);
		assertEquals(testNode, memory.getClauseOfIndex(5));
		assertEquals(5, memory.getIndexOfClause(testNode));
	}
}
