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

import java.util.LinkedHashSet;
import java.util.Set;

import org.junit.Test;
import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

/**
 * Tests for {@link MusExtractor}.
 *
 * @author Timo G&uuml;nther
 */
public abstract class MusExtractorTests extends MutableSatSolverTests {

	@Test
	public void testMus() {
		final MusExtractor solver = getInstance();
		solver.addFormula(new And("A", new Or(new Not("A"), "B"), "C", new Or("C", new Not("D")), new Not("B")));
		final Set<Node> expected = new LinkedHashSet<>();
		expected.add(new Or("A"));
		expected.add(new Or(new Literal("A", false), "B"));
		expected.add(new Or(new Literal("B", false)));
		final Set<Node> actual = solver.getMinimalUnsatisfiableSubset();
		assertEquals(expected, actual);
	}

	@Test
	public void testMusEmpty() {
		final MusExtractor solver = getInstance();
		exception.expect(IllegalStateException.class);
		solver.getMinimalUnsatisfiableSubset();
	}

	@Test
	public void testMusContradiction() {
		final MusExtractor solver = getInstance();
		solver.addFormula(new And("A", new Literal("A", false)));
		final Set<Node> expected = new LinkedHashSet<>();
		expected.add(new Or("A"));
		expected.add(new Or(new Literal("A", false)));
		final Set<Node> actual = solver.getMinimalUnsatisfiableSubset();
		assertEquals(expected, actual);
	}

	@Test
	public void testMusSatisfiable() {
		final MusExtractor solver = getInstance();
		solver.addFormula(new And("A", new Literal("B", false)));
		exception.expect(IllegalStateException.class);
		solver.getMinimalUnsatisfiableSubset();
	}

	@Test
	public void testMusAssumptions() {
		final MusExtractor solver = getInstance();
		solver.addFormula(new And("A", "B"));
		solver.addAssumption("A", false);
		final Set<Node> expected = new LinkedHashSet<>();
		expected.add(new Or("A"));
		final Set<Node> actual = solver.getMinimalUnsatisfiableSubset();
		assertEquals(expected, actual);
	}

	@Override
	protected abstract MusExtractor getInstance();
}
