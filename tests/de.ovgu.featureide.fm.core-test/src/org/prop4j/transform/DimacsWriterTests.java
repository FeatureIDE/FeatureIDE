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
package org.prop4j.transform;

import static org.junit.Assert.assertEquals;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.io.dimacs.DimacsWriter;

/**
 * Tests for {@link DimacsWriter}.
 *
 * @author Timo G&uuml;nther
 */
public class DimacsWriterTests {

	private static final String LN = System.lineSeparator();

	@Rule
	public final ExpectedException exception = ExpectedException.none();

	@Test
	public void testSimple() {
		testEquals(new And(new Or("A", new Literal("B", false)), new Or("C", "B", new Literal("A", false))));
	}

	@Test
	public void testVariablesFoo() {
		testEquals(new And(new Or("Foo", new Literal("Bar", false)), new Or("Baz", "Bar", new Literal("Foo", false))));
	}

	@Test
	public void testVariablesNumbersStrings() {
		testEquals(new And(new Or("1", new Literal("2", false)), new Or("3", "2", new Literal("1", false))));
	}

	@Test
	public void testVariablesNumbersIntegers() {
		testEquals(new And(new Or(1, new Literal(2, false)), new Or(3, 2, new Literal(1, false))));
	}

	@Test
	public void testAnd() {
		testEquals(new And("A", new Literal("B", false)), "p cnf 2 2" + LN + "1 0" + LN + "-2 0" + LN);
	}

	@Test
	public void testOr() {
		testEquals(new Or(new Literal("A", false), "B"), "p cnf 2 1" + LN + "-1 2 0" + LN);
	}

	@Test
	public void testNotLiteral() {
		testEquals(new Literal("A", false), "p cnf 1 1" + LN + "-1 0" + LN);
	}

	@Test
	public void testNotNode() {
		final Node in = new Not("A");
		exception.expect(IllegalArgumentException.class);
		new DimacsWriter().write(in);
	}

	@Test
	public void testImplies() {
		final Node in = new Implies("A", "B");
		exception.expect(IllegalArgumentException.class);
		new DimacsWriter().write(in);
	}

	@Test
	public void testNull() {
		final Node in = null;
		exception.expect(IllegalArgumentException.class);
		new DimacsWriter().write(in);
	}

	@Test
	public void testVariableDirectory() {
		final Node in = new And(new Or("A", new Literal("B", false)), new Or("C", "B", new Literal("A", false)));
		final DimacsWriter w = new DimacsWriter();
		w.setWritingVariableDirectory(true);
		final String actual = w.write(in);
		final String expected = "c 1 A" + LN + "c 2 B" + LN + "c 3 C" + LN + getDefaultExpected();
		assertEquals(expected, actual);
	}

	private void testEquals(Node in) {
		testEquals(in, getDefaultExpected());
	}

	private void testEquals(Node in, String expected) {
		final DimacsWriter w = new DimacsWriter();
		final String actual = w.write(in);
		assertEquals(expected, actual);
	}

	private String getDefaultExpected() {
		return "p cnf 3 2" + LN + "1 -2 0" + LN + "3 2 -1 0" + LN;
	}
}
