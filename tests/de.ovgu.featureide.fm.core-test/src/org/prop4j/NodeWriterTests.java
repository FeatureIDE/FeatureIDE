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

import org.junit.Test;
import org.prop4j.NodeWriter.Notation;

/**
 * Tests for {@link NodeWriter}.
 *
 * @author Timo G&uuml;nther
 */
public class NodeWriterTests {

	@Test
	public void testSimple() {
		testEquals(new And(new Or("A", new Not("B")), new Or("C", "B", new Not("A"))), "(A | -B) & (C | B | -A)");
	}

	@Test
	public void testLiteral() {
		testEquals(new Literal("A"), "A");
	}

	@Test
	public void testNotNode() {
		testEquals(new Not("A"), "-A");
	}

	@Test
	public void testNotLiteral() {
		testEquals(new Literal("A", false), "-A");
	}

	@Test
	public void testAnd() {
		testEquals(new And("A", "B"), "A & B");
	}

	@Test
	public void testOr() {
		testEquals(new Or("A", "B"), "A | B");
	}

	@Test
	public void testImplies() {
		testEquals(new Implies("A", "B"), "A => B");
	}

	@Test
	public void testEquals() {
		testEquals(new Equals("A", "B"), "A <=> B");
	}

	@Test
	public void testChoose() {
		testEquals(new Choose(2, "A", "B", "C", "D", "E"), "choose2(A, B, C, D, E)");
	}

	@Test
	public void testAtLeast() {
		testEquals(new AtLeast(3, "A", "B", "C", "D", "E"), "atleast3(A, B, C, D, E)");
	}

	@Test
	public void testAtMost() {
		testEquals(new AtMost(4, "A", "B", "C", "D", "E"), "atmost4(A, B, C, D, E)");
	}

	@Test
	public void testNestedNotNode() {
		testEquals(new Not(new Not(new Not("A"))), "-(-(-A))");
	}

	@Test
	public void testNestedNotLiteral() {
		/*
		 * Technically, this is just a negated literal that happens to be using another literal as variable. Since a literal has no children and its variable is
		 * not interpreted as a node, this is not the same as nested negations.
		 */
		testEquals(new Literal(new Literal(new Literal("A", false), false), false), "---A");
	}

	@Test
	public void testNestedAnd() {
		testEquals(new And("A", "B", new And("C", new And("D", "E")), "F"), "A & B & C & D & E & F");
	}

	@Test
	public void testNestedOr() {
		testEquals(new Or(new Or("A", new Or("B", "C")), "D", "E", new Or("F", "G")), "A | B | C | D | E | F | G");
	}

	@Test
	public void testNestedImplies() {
		testEquals(new Implies(new Implies("A", new Implies("B", "A")), new Implies(new Implies("B", "C"), "C")), "(A => (B => A)) => ((B => C) => C)");
	}

	@Test
	public void testNestedEquals() {
		testEquals(new Equals(new Equals("A", "B"), new Equals("B", "A")), "A <=> B <=> B <=> A");
	}

	@Test
	public void testNestedChoose() {
		testEquals(new Choose(314, "A", new Choose(3, "A", "B", "C", "D"), "B", "C", "D"), "choose314(A, choose3(A, B, C, D), B, C, D)");
	}

	@Test
	public void testNestedAtLeast() {
		testEquals(new AtLeast(2, "B", new AtLeast(2, "A", "B", new AtLeast(2, "B", "D", "E"), "D"), "D", new AtLeast(4, "A", "B", "C", "D", "E", "F"), "F"),
				"atleast2(B, atleast2(A, B, atleast2(B, D, E), D), D, atleast4(A, B, C, D, E, F), F)");
	}

	@Test
	public void testNestedAtMost() {
		testEquals(new AtMost(2, new AtMost(123, "A", "B"), new AtMost(456, "B", "C")), "atmost2(atmost123(A, B), atmost456(B, C))");
	}

	public void testNull() {
		testEquals(null, "null");
	}

	public void testNullLiteral() {
		testEquals(new Literal(null), "null");
	}

	@Test
	public void testVariablesLetters() {
		testEquals(new And("A", new AtMost(3, "A", "B", "C")), "A & atmost3(A, B, C)");
	}

	@Test
	public void testVariablesFoo() {
		testEquals(new And("Foo", new AtMost(3, "Foo", "Bar", "Baz")), "Foo & atmost3(Foo, Bar, Baz)");
	}

	@Test
	public void testVariablesNumbers() {
		testEquals(new And("5", new AtMost(3, "5", "0", "1234")), "5 & atmost3(5, 0, 1234)");
	}

	@Test
	public void testVariablesIntegers() {
		testEquals(new And(5, new AtMost(3, 5, 0, 1234)), "5 & atmost3(5, 0, 1234)");
	}

	@Test
	public void testOrderNotNot() {
		testEquals(new Not(new Not("A")), "-(-A)");
	}

	@Test
	public void testOrderNotAnd() {
		testEquals(new Not(new And("A", "B")), "-(A & B)");
	}

	@Test
	public void testOrderNotOr() {
		testEquals(new Not(new Or("A", "B")), "-(A | B)");
	}

	@Test
	public void testOrderNotImplies() {
		testEquals(new Not(new Implies("A", "B")), "-(A => B)");
	}

	@Test
	public void testOrderNotEquals() {
		testEquals(new Not(new Equals("A", "B")), "-(A <=> B)");
	}

	@Test
	public void testOrderNotChoose() {
		testEquals(new Not(new Choose(1, "A")), "-(choose1(A))");
	}

	@Test
	public void testOrderNotAtLeast() {
		testEquals(new Not(new AtLeast(1, "A")), "-(atleast1(A))");
	}

	@Test
	public void testOrderNotAtMost() {
		testEquals(new Not(new AtMost(1, "A")), "-(atmost1(A))");
	}

	@Test
	public void testOrderAnd() {
		testEquals(new And(new Not("A"), new And("A", "B"), new Or("A", "B"), new Implies("A", "B"), new Equals("A", "B"), new Choose(1, "A"),
				new AtLeast(1, "A"), new AtMost(1, "A")), "-A & A & B & (A | B) & (A => B) & (A <=> B) & choose1(A) & atleast1(A) & atmost1(A)");
	}

	@Test
	public void testOrderOr() {
		testEquals(new Or(new Not("A"), new And("A", "B"), new Or("A", "B"), new Implies("A", "B"), new Equals("A", "B"), new Choose(1, "A"),
				new AtLeast(1, "A"), new AtMost(1, "A")), "-A | A & B | A | B | (A => B) | (A <=> B) | choose1(A) | atleast1(A) | atmost1(A)");
	}

	@Test
	public void testOrderImpliesNot() {
		testEquals(new Implies(new Not("A"), new Not("A")), "-A => -A");
	}

	@Test
	public void testOrderImpliesAnd() {
		testEquals(new Implies(new And("A", "B"), new And("A", "B")), "A & B => A & B");
	}

	@Test
	public void testOrderImpliesOr() {
		testEquals(new Implies(new Or("A", "B"), new Or("A", "B")), "A | B => A | B");
	}

	@Test
	public void testOrderImpliesImplies() {
		testEquals(new Implies(new Implies("A", "B"), new Implies("A", "B")), "(A => B) => (A => B)");
	}

	@Test
	public void testOrderImpliesEquals() {
		testEquals(new Implies(new Equals("A", "B"), new Equals("A", "B")), "(A <=> B) => (A <=> B)");
	}

	@Test
	public void testOrderImpliesChoose() {
		testEquals(new Implies(new Choose(1, "A"), new Choose(1, "A")), "choose1(A) => choose1(A)");
	}

	@Test
	public void testOrderImpliesAtLeast() {
		testEquals(new Implies(new AtLeast(1, "A"), new AtLeast(1, "A")), "atleast1(A) => atleast1(A)");
	}

	@Test
	public void testOrderImpliesAtMost() {
		testEquals(new Implies(new AtMost(1, "A"), new AtMost(1, "A")), "atmost1(A) => atmost1(A)");
	}

	@Test
	public void testOrderEqualsNot() {
		testEquals(new Equals(new Not("A"), new Not("A")), "-A <=> -A");
	}

	@Test
	public void testOrderEqualsAnd() {
		testEquals(new Equals(new And("A", "B"), new And("A", "B")), "A & B <=> A & B");
	}

	@Test
	public void testOrderEqualsOr() {
		testEquals(new Equals(new Or("A", "B"), new Or("A", "B")), "A | B <=> A | B");
	}

	@Test
	public void testOrderEqualsImplies() {
		testEquals(new Equals(new Implies("A", "B"), new Implies("A", "B")), "A => B <=> A => B");
	}

	@Test
	public void testOrderEqualsEquals() {
		testEquals(new Equals(new Equals("A", "B"), new Equals("A", "B")), "A <=> B <=> A <=> B");
	}

	@Test
	public void testOrderEqualsChoose() {
		testEquals(new Equals(new Choose(1, "A"), new Choose(1, "A")), "choose1(A) <=> choose1(A)");
	}

	@Test
	public void testOrderEqualsAtLeast() {
		testEquals(new Equals(new AtLeast(1, "A"), new AtLeast(1, "A")), "atleast1(A) <=> atleast1(A)");
	}

	@Test
	public void testOrderEqualsAtMost() {
		testEquals(new Equals(new AtMost(1, "A"), new AtMost(1, "A")), "atmost1(A) <=> atmost1(A)");
	}

	@Test
	public void testSymbolsShort() {
		testSymbols(NodeWriter.shortSymbols, "A & B | (B <=> -A) | (-B => C) | choose42(A) | atleast24(C, -(-C), C) | atmost2(B)");
	}

	@Test
	public void testSymbolsTextual() {
		testSymbols(NodeWriter.textualSymbols, "A and B or (B iff not A) or (not B implies C) or choose42(A) or atleast24(C, not (not C), C) or atmost2(B)");
	}

	@Test
	public void testSymbolsLogical() {
		testSymbols(NodeWriter.logicalSymbols,
				"A \u2227 B \u2228 (B \u21D4 \u00ACA) \u2228 (\u00ACB \u21D2 C) \u2228 choose42(A) \u2228 atleast24(C, \u00AC(\u00ACC), C) \u2228 atmost2(B)");
	}

	@Test
	public void testSymbolsJava() {
		testSymbols(NodeWriter.javaSymbols, "A && B || (B == !A) || (!B ? C) || ?42(A) || ?24(C, !(!C), C) || ?2(B)");
	}

	@Test
	public void testNotationInfix() {
		testNotation(Notation.INFIX, "A & B | (B <=> -A) | (-B => C) | choose42(A) | atleast24(C, -(-C), C) | atmost2(B)");
	}

	@Test
	public void testNotationPrefix() {
		testNotation(Notation.PREFIX, "(| (& A B) (<=> B (- A)) (=> (- B) C) (choose42 A) (atleast24 C (- (- C)) C) (atmost2 B))");
	}

	@Test
	public void testNotationPostfix() {
		testNotation(Notation.POSTFIX, "((A B &) (B (A -) <=>) ((B -) C =>) (A choose42) (C ((C -) -) C atleast24) (B atmost2) |)");
	}

	@Test
	public void testEnforceBrackets() {
		final Node in = new Equals(new Implies(new And("A", "B"), "B"), new Or(new And("C", "A"), "B", "B", new Or(new AtMost(2, "C"), "A")));
		final NodeWriter w = new NodeWriter(in);
		String actual = w.nodeToString();
		String expected = "A & B => B <=> C & A | B | B | atmost2(C) | A";
		assertEquals(expected, actual);
		w.setEnforceBrackets(true);
		actual = w.nodeToString();
		expected = "(((A & B) => B) <=> ((C & A) | B | B | (atmost2(C) | A)))";
		assertEquals(expected, actual);
	}

	@Test
	public void testEnquoteWhitespace() {
		final Node in = new And("nowhitespace", "white space", "with\ttab", "with\nnewline", new Not("nowhitespace"), new Not("white space"),
				new Literal("nowhitespace", false), new Literal("white space", false));
		final NodeWriter w = new NodeWriter(in);
		String actual = w.nodeToString();
		String expected = "nowhitespace & white space & with\ttab & with\nnewline & -nowhitespace & -white space & -nowhitespace & -white space";
		assertEquals(expected, actual);
		w.setEnquoteWhitespace(true);
		actual = w.nodeToString();
		expected = "nowhitespace & \"white space\" & \"with\ttab\" & \"with\nnewline\" & -nowhitespace & -\"white space\" & -nowhitespace & -\"white space\"";
		assertEquals(expected, actual);
	}

	private void testSymbols(String[] symbols, String expected) {
		testSymbols(getDefaultIn(), symbols, expected);
	}

	private void testSymbols(Node in, String[] symbols, String expected) {
		final NodeWriter w = new NodeWriter(in);
		w.setSymbols(symbols);
		final String actual = w.nodeToString();
		assertEquals(expected, actual);
	}

	private void testNotation(Notation notation, String expected) {
		testNotation(getDefaultIn(), notation, expected);
	}

	private void testNotation(Node in, Notation notation, String expected) {
		final NodeWriter w = new NodeWriter(in);
		w.setNotation(notation);
		final String actual = w.nodeToString();
		assertEquals(expected, actual);
	}

	private void testEquals(Node in, String expected) {
		final NodeWriter w = new NodeWriter(in);
		final String actual = w.nodeToString();
		assertEquals(expected, actual);
	}

	private Node getDefaultIn() {
		return new Or(new And("A", "B"), new Equals("B", new Not("A")), new Implies(new Literal("B", false), "C"), new Choose(42, "A"),
				new AtLeast(24, "C", new Not(new Not("C")), "C"), new AtMost(2, "B"));
	}
}
