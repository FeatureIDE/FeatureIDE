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

import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.List;

import org.junit.Test;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.impl.SatProblem;
import org.prop4j.solvers.impl.javasmt.MutableSolverMemory;
import org.prop4j.solvers.impl.javasmt.SolverMemory;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Test to check the functionality of {@link SolverMemory}
 *
 * @author Joshua Sprey
 */
public class SolverMemoryTest {

	private final SatProblem problem;
	private final IFeatureModel model;

	public SolverMemoryTest() {
		final Literal A = new Literal("A");
		model = Commons.loadTestFeatureModelFromFile("car.xml");
		problem = new SatProblem(model.getAnalyser().getCnf());
	}

	public MutableSolverMemory<Node, Node> getNewEmptyMemory() {
		return new MutableSolverMemory<>();
	}

	public MutableSolverMemory<Node, Node> getNewFilledMemory(boolean isAnAssumptionAClause) {
		return new MutableSolverMemory<>(problem, Arrays.asList(problem.getClauses()), isAnAssumptionAClause);
	}

	@Test
	public void testAddVariable() {
		final MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		int result = memory.addVariable("Test Test");
		assertTrue(result == 17);
		result = memory.addVariable("Test 2");
		assertTrue(result == 18);
		result = memory.addVariable("Test 3");
		assertTrue(result == 19);

		// Add again all three => should return 0 meaning already present
		result = memory.addVariable("Test Test");
		assertTrue(result == 0);
		result = memory.addVariable("Test 2");
		assertTrue(result == 0);
		result = memory.addVariable("Test 3");
		assertTrue(result == 0);

		// Check that all feature are already registered as variables
		for (int i = 0; i < problem.getNumberOfVariables(); i++) {
			final Object var = problem.getVariableOfIndex(i);
			if (var instanceof String) {
				result = memory.addVariable((String) var);
				assertTrue(result == 0);
			}

		}
	}

	@Test
	public void testGetAssumptionsAsList() {
		final MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		final Literal assumption1 = new Literal("USB", true);
		final Literal assumption2 = new Literal("CD", false);
		final Literal assumption3 = new Literal("Europe", true);
		final Literal assumption4 = new Literal("Manual", false);

		assertTrue(memory.getAssumptionsAsList().size() == 0);
		// Push some assumptions
		memory.pushAssumption(assumption1, assumption1);
		assertTrue(memory.getAssumptionsAsList().size() == 1);
		memory.pushAssumption(assumption2, assumption2);
		assertTrue(memory.getAssumptionsAsList().size() == 2);
		memory.pushAssumption(assumption3, assumption3);
		assertTrue(memory.getAssumptionsAsList().size() == 3);
		memory.pushAssumption(assumption4, assumption4);
		assertTrue(memory.getAssumptionsAsList().size() == 4);

		// Get all assumptions
		final List<Node> assumptions = memory.getAssumptionsAsList();
		// Check that assuptions nodes are always literals
		for (final Node assumption : assumptions) {
			assertTrue(assumption instanceof Literal);
		}
	}

	@Test
	public void testGetClauseOfIndex() {
		MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		for (final Node clause : memory.getClausesAsList()) {
			assertTrue(clause instanceof Or);
		}

		Node clauseOrig = problem.getClauses()[6];
		Node clauseTemp = memory.getClauseOfIndex(6);
		assertTrue(clauseOrig == clauseTemp);

		clauseOrig = problem.getClauses()[0];
		clauseTemp = memory.getClauseOfIndex(0);
		assertTrue(clauseOrig == clauseTemp);

		clauseOrig = problem.getClauses()[problem.getClauseCount() - 1];
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount() - 1);
		assertTrue(clauseOrig == clauseTemp);

		// Add new clause
		Or newClause = new Or(new Literal("GearboxTest"), new Literal("Bluetooth"));
		memory.push(newClause, newClause);
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount());
		assertTrue(newClause == clauseTemp);

		// Remove clause
		memory.pop();
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount());
		assertTrue(clauseTemp == null);

		// Add new assumption (memory is currently set to recognize assumptions as clauses)
		Literal newAssumption = new Literal("GearboxTest", true);
		memory.pushAssumption(newAssumption, newAssumption);
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount());
		assertTrue(clauseTemp == newAssumption);

		// Remove assumption
		memory.pop();
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount());
		assertTrue(clauseTemp == null);

		// Add both
		memory.push(newClause, newClause);
		memory.pushAssumption(newAssumption, newAssumption);
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount());
		assertTrue(clauseTemp == newClause);
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount() + 1);
		assertTrue(clauseTemp == newAssumption);

		// Now the same but now the assumptions are not recognized as clauses
		memory = getNewFilledMemory(false);

		for (final Node clause : memory.getClausesAsList()) {
			assertTrue(clause instanceof Or);
		}

		clauseOrig = problem.getClauses()[6];
		clauseTemp = memory.getClauseOfIndex(6);
		assertTrue(clauseOrig == clauseTemp);

		clauseOrig = problem.getClauses()[0];
		clauseTemp = memory.getClauseOfIndex(0);
		assertTrue(clauseOrig == clauseTemp);

		clauseOrig = problem.getClauses()[problem.getClauseCount() - 1];
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount() - 1);
		assertTrue(clauseOrig == clauseTemp);

		// Add new clause
		newClause = new Or(new Literal("GearboxTest"), new Literal("Bluetooth"));
		memory.push(newClause, newClause);
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount());
		assertTrue(newClause == clauseTemp);

		// Remove clause
		memory.pop();
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount());
		assertTrue(clauseTemp == null);

		// Add new assumption (memory is currently set to not recognize assumptions as clauses)
		newAssumption = new Literal("GearboxTest", true);
		memory.pushAssumption(newAssumption, newAssumption);
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount());
		assertTrue(clauseTemp == null);

		// Remove assumption
		memory.pop();
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount());
		assertTrue(clauseTemp == null);

		// Add both
		memory.push(newClause, newClause);
		memory.pushAssumption(newAssumption, newAssumption);
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount());
		assertTrue(clauseTemp == newClause);
		clauseTemp = memory.getClauseOfIndex(problem.getClauseCount() + 1);
		assertTrue(clauseTemp == null);
	}

	@Test
	public void testGetClausesAsNodeList() {
		MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		assertTrue(memory.getClausesAsNodeList().size() == problem.getClauseCount());

		// Add new Clause
		final Node newClause = new Or(new Literal("GearboxTest"), new Literal("Bluetooth"));
		memory.push(newClause, newClause);
		assertTrue(memory.getClausesAsNodeList().contains(newClause));
		memory.pop();
		assertTrue(!memory.getClausesAsNodeList().contains(newClause));

		// Add new assumption (memory is currently set to recognize assumptions as clauses)
		final Literal newAssumption = new Literal("GearboxTest", true);
		memory.pushAssumption(newAssumption, newAssumption);
		assertTrue(memory.getClausesAsNodeList().contains(newAssumption));
		memory.pop();
		assertTrue(!memory.getClausesAsNodeList().contains(newAssumption));

		memory = getNewFilledMemory(false);
		// Add new assumption (memory is currently set to not recognize assumptions as clauses)
		memory.pushAssumption(newAssumption, newAssumption);
		assertTrue(!memory.getClausesAsNodeList().contains(newAssumption));
		memory.pop();
		assertTrue(!memory.getClausesAsNodeList().contains(newAssumption));
	}

	@Test
	public void testGetIndexOfClause() {
		MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		for (final Node clause : memory.getClausesAsList()) {
			assertTrue(clause instanceof Or);
		}

		for (int i = 0; i < memory.getClausesAsList().size(); i++) {
			assertTrue(memory.getClauseOfIndex(i) != null);
			assertTrue(memory.getClauseOfIndex(i) instanceof Or);
		}

		// Add new clause
		Or newClause = new Or(new Literal("GearboxTest"), new Literal("Bluetooth"));
		memory.push(newClause, newClause);
		int index = memory.getIndexOfClause(newClause);
		assertTrue(index == problem.getClauseCount());

		// Remove clause
		memory.pop();
		index = memory.getIndexOfClause(newClause);
		assertTrue(index == -1);

		// Add new assumption (memory is currently set to recognize assumptions as clauses)
		Literal newAssumption = new Literal("GearboxTest", true);
		memory.pushAssumption(newAssumption, newAssumption);
		index = memory.getIndexOfClause(newAssumption);
		assertTrue(index == problem.getClauseCount());

		// Remove assumption
		memory.pop();
		index = memory.getIndexOfClause(newAssumption);
		assertTrue(index == -1);

		// Add both
		memory.push(newClause, newClause);
		memory.pushAssumption(newAssumption, newAssumption);
		index = memory.getIndexOfClause(newClause);
		assertTrue(index == problem.getClauseCount());
		index = memory.getIndexOfClause(newAssumption);
		assertTrue(index == (problem.getClauseCount() + 1));

		// Now the same but now the assumptions are not recognized as clauses
		memory = getNewFilledMemory(false);

		// Add new clause
		newClause = new Or(new Literal("GearboxTest"), new Literal("Bluetooth"));
		memory.push(newClause, newClause);
		index = memory.getIndexOfClause(newClause);
		assertTrue(index == problem.getClauseCount());

		// Remove clause
		memory.pop();
		index = memory.getIndexOfClause(newClause);
		assertTrue(index == -1);

		// Add new assumption (memory is currently set to recognize assumptions as clauses)
		newAssumption = new Literal("GearboxTest", true);
		memory.pushAssumption(newAssumption, newAssumption);
		index = memory.getIndexOfClause(newAssumption);
		assertTrue(index == -1);

		// Remove assumption
		memory.pop();
		index = memory.getIndexOfClause(newAssumption);
		assertTrue(index == -1);

		// Add both
		memory.push(newClause, newClause);
		memory.pushAssumption(newAssumption, newAssumption);
		index = memory.getIndexOfClause(newClause);
		assertTrue(index == problem.getClauseCount());
		index = memory.getIndexOfClause(newAssumption);
		assertTrue(index == -1);
	}

	@Test
	public void testGetIndexOfVariable() {
		final MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		for (final IFeature feature : model.getFeatures()) {
			final String featureName = feature.getName();
			final int index = memory.getIndexOfVariable(featureName);
			assertTrue(index != 0);
		}

		final String testString = "Test Test";
		final int result = memory.addVariable(testString);
		assertTrue(result == 17);
		final int resultTemp = memory.getIndexOfVariable(testString);
		assertTrue(result == resultTemp);
	}

	@Test
	public void testGetSingedIndexOfVariable() {
		final MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		for (final IFeature feature : model.getFeatures()) {
			final String featureName = feature.getName();
			final Literal newLit = new Literal(featureName, (Math.random() * 2) < 1 ? true : false);
			final int indexOrig = memory.getIndexOfVariable(featureName);
			final int indexSigned = memory.getSingedIndexOfVariable(newLit);
			assertTrue(indexOrig == Math.abs(indexSigned));
			if (newLit.positive) {
				assertTrue(indexOrig == indexSigned);
			} else {
				assertTrue(indexOrig == -indexSigned);
			}
		}
	}

	@Test
	public void testGetVariableOfIndex() {
		final MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		final String test = "Test Test";
		final int result = memory.addVariable(test);
		assertTrue(result == 17);

		Object var = memory.getVariableOfIndex(result);
		assertTrue(var == test);

		// Variable index 0 is always null
		var = memory.getVariableOfIndex(0);
		assertTrue(var == null);
	}

	@Test
	public void testIsNextPopAssumption() {
		final MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		assertTrue(!memory.isNextPopAssumption());

		// add clause
		final Node newClause = new Or(new Literal("GearboxTest"), new Literal("Bluetooth"));
		memory.push(newClause, newClause);
		assertTrue(!memory.isNextPopAssumption());

		// Add Assumption
		final Literal newAssumption = new Literal("GearboxTest");
		memory.pushAssumption(newAssumption, newAssumption);
		assertTrue(memory.isNextPopAssumption());

		// add another clause
		final Node newClause2 = new Or(new Literal("AAA"), new Literal("BBB"));
		memory.push(newClause2, newClause2);
		assertTrue(!memory.isNextPopAssumption());

		memory.pop();
		assertTrue(memory.isNextPopAssumption());
		memory.pop();
		assertTrue(!memory.isNextPopAssumption());
		memory.pushAssumption(newAssumption, newAssumption);
		assertTrue(memory.isNextPopAssumption());
	}

	@Test
	public void testIsVariablePresent() {
		final MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		for (final IFeature feature : model.getFeatures()) {
			final String featureName = feature.getName();
			assertTrue(memory.isVariablePresent(featureName));
		}
		final String testVar = "Test Test";
		assertTrue(!memory.isVariablePresent(testVar));
		memory.addVariable(testVar);
		assertTrue(memory.isVariablePresent(testVar));
	}

	@Test
	public void testPeekNextNode() {
		final MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		assertTrue(memory.peekNextNode() == null);

		// add clause
		final Node newClause = new Or(new Literal("GearboxTest"), new Literal("Bluetooth"));
		memory.push(newClause, newClause);
		assertTrue((memory.peekNextNode() instanceof Or));

		// Add Assumption
		final Literal newAssumption = new Literal("GearboxTest");
		memory.pushAssumption(newAssumption, newAssumption);
		assertTrue((memory.peekNextNode() instanceof Literal));

		// add another clause
		final Node newClause2 = new Or(new Literal("AAA"), new Literal("BBB"));
		memory.push(newClause2, newClause2);
		assertTrue((memory.peekNextNode() instanceof Or));

		memory.pop();
		assertTrue((memory.peekNextNode() instanceof Literal));
		memory.pop();
		assertTrue((memory.peekNextNode() instanceof Or));
		memory.pushAssumption(newAssumption, newAssumption);
		assertTrue((memory.peekNextNode() instanceof Literal));
	}

	@Test
	public void testPop() {
		final MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		final Literal newAssumption = new Literal("GearboxTest", true);
		final Literal newAssumption2 = new Literal("Bluetooth", true);
		final Node newClause1 = new Or(new Literal("GearboxTest"), new Literal("Bluetooth"));
		final Node newClause2 = new Or(new Literal("AAA"), new Literal("BBB"));

		assertTrue(memory.pop() == null);

		// Check Assumptions
		memory.pushAssumption(newAssumption, newAssumption);
		assertTrue(memory.pop() == newAssumption);
		memory.pushAssumption(newAssumption, newAssumption);
		memory.pushAssumption(newAssumption2, newAssumption2);
		assertTrue(memory.pop() == newAssumption2);
		assertTrue(memory.pop() == newAssumption);

		// Check clauses
		memory.push(newClause1, newClause1);
		assertTrue(memory.pop() == newClause1);
		memory.push(newClause1, newClause1);
		memory.push(newClause2, newClause2);
		assertTrue(memory.pop() == newClause2);
		assertTrue(memory.pop() == newClause1);

		// Check both
		memory.push(newClause1, newClause1);
		memory.pushAssumption(newAssumption, newAssumption);
		memory.push(newClause2, newClause2);
		memory.pushAssumption(newAssumption2, newAssumption2);
		assertTrue(memory.pop() == newAssumption2);
		assertTrue(memory.pop() == newClause2);
		assertTrue(memory.pop() == newAssumption);
		assertTrue(memory.pop() == newClause1);
	}

	@Test
	public void testPopAssumption() {
		final MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		final Literal newAssumption = new Literal("GearboxTest", true);
		final Literal newAssumption2 = new Literal("Bluetooth", true);
		final Node newClause1 = new Or(new Literal("GearboxTest"), new Literal("Bluetooth"));
		final Node newClause2 = new Or(new Literal("AAA"), new Literal("BBB"));

		assertTrue(memory.popAssumption() == null);

		// Check Assumptions
		memory.pushAssumption(newAssumption, newAssumption);
		assertTrue(memory.popAssumption() == newAssumption);
		memory.pushAssumption(newAssumption, newAssumption);
		memory.pushAssumption(newAssumption2, newAssumption2);
		assertTrue(memory.popAssumption() == newAssumption2);
		assertTrue(memory.popAssumption() == newAssumption);

		// Check clauses
		memory.push(newClause1, newClause1);
		assertTrue(memory.popAssumption() == null);
		memory.pop();
		memory.push(newClause1, newClause1);
		memory.push(newClause2, newClause2);
		assertTrue(memory.popAssumption() == null);
		memory.pop();
		assertTrue(memory.popAssumption() == null);
		memory.pop();

		// Check both
		memory.push(newClause1, newClause1);
		memory.pushAssumption(newAssumption, newAssumption);
		memory.push(newClause2, newClause2);
		memory.pushAssumption(newAssumption2, newAssumption2);
		assertTrue(memory.popAssumption() == newAssumption2);
		assertTrue(memory.popAssumption() == null);
		memory.pop();
		assertTrue(memory.popAssumption() == newAssumption);
		assertTrue(memory.popAssumption() == null);
		memory.pop();
	}

	@Test
	public void testPopClause() {
		final MutableSolverMemory<Node, Node> memory = getNewFilledMemory(true);

		final Literal newAssumption = new Literal("GearboxTest", true);
		final Literal newAssumption2 = new Literal("Bluetooth", true);
		final Node newClause1 = new Or(new Literal("GearboxTest"), new Literal("Bluetooth"));
		final Node newClause2 = new Or(new Literal("AAA"), new Literal("BBB"));

		assertTrue(memory.popClause() == null);

		// Check Assumptions
		memory.pushAssumption(newAssumption, newAssumption);
		assertTrue(memory.popClause() == null);
		memory.pop();
		memory.pushAssumption(newAssumption, newAssumption);
		memory.pushAssumption(newAssumption2, newAssumption2);
		assertTrue(memory.popClause() == null);
		memory.pop();
		assertTrue(memory.popClause() == null);
		memory.pop();

		// Check clauses
		memory.push(newClause1, newClause1);
		assertTrue(memory.popClause() == newClause1);
		memory.push(newClause1, newClause1);
		memory.push(newClause2, newClause2);
		assertTrue(memory.popClause() == newClause2);
		assertTrue(memory.popClause() == newClause1);

		// Check both
		memory.push(newClause1, newClause1);
		memory.pushAssumption(newAssumption, newAssumption);
		memory.push(newClause2, newClause2);
		memory.pushAssumption(newAssumption2, newAssumption2);
		assertTrue(memory.popClause() == null);
		memory.pop();
		assertTrue(memory.popClause() == newClause2);
		assertTrue(memory.popClause() == null);
		memory.pop();
		assertTrue(memory.popClause() == newClause1);
	}
}
