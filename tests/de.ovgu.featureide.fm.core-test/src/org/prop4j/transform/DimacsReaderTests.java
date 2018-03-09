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

import java.io.IOException;
import java.text.ParseException;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.io.dimacs.DimacsReader;

/**
 * Tests for {@link DimacsReader}.
 *
 * @author Timo G&uuml;nther
 */
public class DimacsReaderTests {

	@Rule
	public final ExpectedException exception = ExpectedException.none();

	@Test
	public void testSimple() throws ParseException, IOException {
		testEquals("" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testWhitespaceLinebreakEnd() throws ParseException, IOException {
		testEquals("" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0\n" + "");
	}

	@Test
	public void testWhitespaceLinebreakNone() throws ParseException, IOException {
		testEquals("" + "p cnf 3 2 1 -3 0 2 3 -1 0");
	}

	@Test
	public void testWhitespaceLinebreakMultiple() throws ParseException, IOException {
		testEquals("" + "p cnf 3 2\n" + "1 -3 0\n\n\n \n \n\n" + "2 3 -1 0");
	}

	@Test
	public void testWhitespaceLinebreakMiddleLine() throws ParseException, IOException {
		testEquals("" + "p cnf 3 2\n" + "1\n-3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testWhitespaceTab() throws ParseException, IOException {
		testEquals("" + "p\tcnf\t3\t2\n" + "1\t-3\t0\t\n" + "2\t3\t-1\t0");
	}

	@Test
	public void testWhitespaceMixed() throws ParseException, IOException {
		testEquals("" + "p cnf 3\t2\n" + "1\t-3 0\n" + "2 3\t-1 0");
	}

	@Test
	public void testWhitespaceLeading() throws ParseException, IOException {
		testEquals("" + "  p cnf 3 2\n" + "  1 -3 0\n" + "  2 3 -1 0");
	}

	@Test
	public void testWhitespaceTrailing() throws ParseException, IOException {
		testEquals("" + "  p cnf 3 2\n  " + "  1 -3 0  \n" + "  2 3 -1 0  ");
	}

	@Test
	public void testWhitespaceIndent() throws ParseException, IOException {
		exception.expect(ParseException.class);
		new DimacsReader().read("" + "p\n" + "  cnf\n" + "    3\n" + "    2\n" + "  1 -3 0\n" + "  2 3 -1 0");
	}

	@Test
	public void testComment() throws ParseException, IOException {
		testEquals("" + "c Hello! My name is Test Case. Nice to meet you!\n" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testCommentEmpty() throws ParseException, IOException {
		testEquals("" + "c\n" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testCommentSpace() throws ParseException, IOException {
		testEquals("" + "c \n" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testCommentSpaceMissing() throws ParseException, IOException {
		testException("" + "cWhere is my space?" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0\n");
	}

	@Test
	public void testCommentMultiple() throws ParseException, IOException {
		testEquals("" + "c\n" + "c multiple comments\n" + "c\n" + "c like, really many\n" + "c\n" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testCommentMiddleFile() throws ParseException, IOException {
		testEquals("" + "p cnf 3 2\n" + "c this comment is hiding in the middle of the file\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testCommentMiddleClauses() throws ParseException, IOException {
		testEquals("" + "p cnf 3 2\n" + "1 -3 0\n" + "c this comment is being even more sneaky\n" + "2 3 -1 0");
	}

	@Test
	public void testCommentMiddleClause() throws ParseException, IOException {
		exception.expect(ParseException.class);
		new DimacsReader().read("" + "p cnf 3 2\n" + "1 c this comment tops them all\n" + "-3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testCommentMiddleProblem() throws ParseException, IOException {
		exception.expect(ParseException.class);
		new DimacsReader().read("" + "p cnf c another rebellious comment\n" + "3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testCommentInline() throws ParseException, IOException {
		testException("" + "p cnf 3 2\n" + "1 c this looks like it might work, but no c -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testCommentEnd() throws ParseException, IOException {
		testEquals("" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0\n" + "c Bye!");
	}

	@Test
	public void testCommentTokenMissing() throws ParseException, IOException {
		testException("" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0\n" + "Bye, correctness!");
	}

	@Test
	public void testCaseSensitiveProblemToken() throws ParseException, IOException {
		testException("" + "P cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testCaseSensitiveProblemType() throws ParseException, IOException {
		testException("" + "p CNF 3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testCaseSensitiveCommentToken() throws ParseException, IOException {
		testException("" + "C this comment thinks it's important\n" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testClauseEndTokenMissing() throws ParseException, IOException {
		testEquals("" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1");
	}

	@Test
	public void testClauseEndTokenMissingTrailing() throws ParseException, IOException {
		testException("" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1\n" + "Just tagging along");
	}

	@Test
	public void testClauseEndTokenMissingComment() throws ParseException, IOException {
		testEquals("" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1\n" + "c I don't have a token for ending clauses, but at least I have a comment");
	}

	@Test
	public void testClauseEndTokenMissingCommentTrailing() throws ParseException, IOException {
		testException("" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1\n" + "c I'm being followed\n" + "by trailing data");
	}

	@Test
	public void testProblemTokenMissing() throws ParseException, IOException {
		testException("" + "cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testProblemTypeMissing() throws ParseException, IOException {
		testException("" + "p 3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testProblemTypeWrong() throws ParseException, IOException {
		testException("" + "p wrong 3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testProblemVariableCountZero() throws ParseException, IOException {
		testException("" + "p cnf 0 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testProblemVariableCountNegative() throws ParseException, IOException {
		testException("" + "p cnf -3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testProblemVariableCountTooHigh() throws ParseException, IOException {
		testException("" + "p cnf 4 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testProblemVariableCountTooLow() throws ParseException, IOException {
		testException("" + "p cnf 2 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testProblemClauseCountZero() throws ParseException, IOException {
		testException("" + "p cnf 3 0\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testProblemClauseCountNegative() throws ParseException, IOException {
		testException("" + "p cnf 3 -2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testProblemClauseCountTooHigh() throws ParseException, IOException {
		testException("" + "p cnf 3 3\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testProblemClauseCountTooLow() throws ParseException, IOException {
		testException("" + "p cnf 3 1\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testEmpty() throws ParseException, IOException {
		testException("");
	}

	@Test
	public void testClausesMissing() throws ParseException, IOException {
		testException("" + "p cnf 0 0");
	}

	@Test
	public void testProblemMissing() throws ParseException, IOException {
		testException("" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testMultiple() throws ParseException, IOException {
		testException("" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0\n" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0");
	}

	@Test
	public void testIndexStart() throws ParseException, IOException {
		testEquals("" + "p cnf 3 2\n" + "11 -13 0\n" + "12 13 -11 0",
				new And(new Or("11", new Literal("13", false)), new Or("12", "13", new Literal("11", false))));
	}

	@Test
	public void testIndexGap() throws ParseException, IOException {
		testEquals("" + "p cnf 3 2\n" + "1 -4 0\n" + "2 4 -1 0", new And(new Or("1", new Literal("4", false)), new Or("2", "4", new Literal("1", false))));
	}

	@Test
	public void testIndexDuplicates() throws ParseException, IOException {
		testEquals("" + "p cnf 1 2\n" + "1 -1 0\n" + "1 1 -1 0", new And(new Or("1", new Literal("1", false)), new Or("1", "1", new Literal("1", false))));
	}

	@Test
	public void testSequential() throws ParseException, IOException {
		final String s = "" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0";
		final DimacsReader r = new DimacsReader();
		assertEquals(r.read(s), getDefaultExpected());
		assertEquals(r.read(s), getDefaultExpected());
	}

	@Test
	public void testVariableDirectoryFoo() throws ParseException, IOException {
		final String s = "" + "c 1 Foo\n" + "c 2 Bar\n" + "c 3 Baz\n" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0";
		final DimacsReader r = new DimacsReader();
		r.setReadingVariableDirectory(true);
		final Node actual = r.read(s);
		final Node expected = new And(new Or("Foo", new Literal("Baz", false)), new Or("Bar", "Baz", new Literal("Foo", false)));
		assertEquals(expected, actual);
	}

	@Test
	public void testVariableDirectoryWhitespace() throws ParseException, IOException {
		final String s = "" + "c 1 Variable\twith\twhitespace\n" + "c 2  \n" + "c 3   Surrounding whitespace  \n" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0";
		final DimacsReader r = new DimacsReader();
		r.setReadingVariableDirectory(true);
		final Node actual = r.read(s);
		final Node expected = new And(new Or("Variable\twith\twhitespace", new Literal("  Surrounding whitespace  ", false)),
				new Or(" ", "  Surrounding whitespace  ", new Literal("Variable\twith\twhitespace", false)));
		assertEquals(expected, actual);
	}

	@Test
	public void testVariableDirectoryFormat() throws ParseException, IOException {
		final String s = "" + "c 1\n" + "c 2 \n" + "c\t\t3 c 3 Foo\n" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0";
		final DimacsReader r = new DimacsReader();
		r.setReadingVariableDirectory(true);
		final Node actual = r.read(s);
		final Node expected = new And(new Or("1", new Literal("c 3 Foo", false)), new Or("2", "c 3 Foo", new Literal("1", false)));
		assertEquals(expected, actual);
	}

	@Test
	public void testVariableDirectoryOrder() throws ParseException, IOException {
		final String s = "" + "c 3 Baz\n" + "c 2 Bar\n" + "c 1 Foo\n" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0";
		final DimacsReader r = new DimacsReader();
		r.setReadingVariableDirectory(true);
		final Node actual = r.read(s);
		final Node expected = new And(new Or("Foo", new Literal("Baz", false)), new Or("Bar", "Baz", new Literal("Foo", false)));
		assertEquals(expected, actual);
	}

	@Test
	public void testVariableDirectoryMultiple() throws ParseException, IOException {
		final String s = "" + "c 1 Foo\n" + "c 1 Overwritten\n" + "c 2 Bar\n" + "c 3 Baz\n" + "p cnf 3 2\n" + "1 -3 0\n" + "2 3 -1 0";
		final DimacsReader r = new DimacsReader();
		r.setReadingVariableDirectory(true);
		final Node actual = r.read(s);
		final Node expected = new And(new Or("Foo", new Literal("Baz", false)), new Or("Bar", "Baz", new Literal("Foo", false)));
		assertEquals(expected, actual);
	}

	@Test
	public void testVariableDirectoryMiddle() throws ParseException, IOException {
		final String s = "" + "p cnf 3 2\n" + "c 1 Foo\n" + "c 2 Bar\n" + "c 3 Baz\n" + "1 -3 0\n" + "2 3 -1 0";
		final DimacsReader r = new DimacsReader();
		r.setReadingVariableDirectory(true);
		final Node actual = r.read(s);
		final Node expected = new And(new Or("Foo", new Literal("Baz", false)), new Or("Bar", "Baz", new Literal("Foo", false)));
		assertEquals(expected, actual);
	}

	@Test
	public void testVariableDirectorySplit() throws ParseException, IOException {
		final String s = "" + "c 1 Foo\n" + "c 2 Bar\n" + "p cnf 3 2\n" + "c 3 Baz\n" + "1 -3 0\n" + "2 3 -1 0";
		final DimacsReader r = new DimacsReader();
		r.setReadingVariableDirectory(true);
		final Node actual = r.read(s);
		final Node expected = new And(new Or("Foo", new Literal("Baz", false)), new Or("Bar", "Baz", new Literal("Foo", false)));
		assertEquals(expected, actual);
	}

	@Test
	public void testVariableDirectoryStraggler() throws ParseException, IOException {
		final String s = "" + "c 1 Foo\n" + "c 2 Bar\n" + "p cnf 3 2\n" + "1 -3 0\n" + "c 3 Baz\n" + "2 3 -1 0";
		final DimacsReader r = new DimacsReader();
		r.setReadingVariableDirectory(true);
		final Node actual = r.read(s);
		final Node expected = new And(new Or("Foo", new Literal("3", false)), new Or("Bar", "3", new Literal("Foo", false)));
		assertEquals(expected, actual);
	}

	private void testEquals(String s) throws ParseException, IOException {
		testEquals(s, getDefaultExpected());
	}

	private void testEquals(String s, Node expected) throws ParseException, IOException {
		final Node actual = new DimacsReader().read(s);
		assertEquals(expected, actual);
	}

	private void testException(String s) throws ParseException, IOException {
		exception.expect(ParseException.class);
		new DimacsReader().read(s);
	}

	private Node getDefaultExpected() {
		return new And(new Or("1", new Literal("3", false)), new Or("2", "3", new Literal("1", false)));
	}
}
