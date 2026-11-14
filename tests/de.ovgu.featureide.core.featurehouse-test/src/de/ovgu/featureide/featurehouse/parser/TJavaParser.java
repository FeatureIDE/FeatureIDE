/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.io.StringReader;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import cide.gparser.OffsetCharStream;
import cide.gparser.ParseException;
import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;
import de.ovgu.cide.fstgen.parsers.generated_java15.Java15Parser;

/**
 * Tests that the Java grammar of FeatureHouse (featurehouse-grammar/java15.jj in de.ovgu.featureide.core.featurehouse) accepts Java syntax that was added after
 * Java 1.5 inside methods and field initializers.
 *
 * Each case is a class member. The test parses a class containing the member and checks that FeatureHouse creates a node for it whose text is exactly the
 * member's source code, because FeatureHouse composes and prints the members with this text.
 *
 * @author Philipp Hehnle
 */
@RunWith(Parameterized.class)
public class TJavaParser {

	@Parameters(name = "{0}")
	public static Collection<Object[]> members() {
		return Arrays.asList(new Object[][] {
			// Java 1.5: must keep working
			{ "Java 5 generics and for-each", "int sum(java.util.List<? extends Number> list) { int s = 0; for (final Number n : list) { s += n.intValue(); } return s; }" },
			{ "Java 5 post-decrement before greater-than", "void countDown() { int i = 10; while (i-->0) { } }" },
			{ "Java 5 bitwise and in parentheses", "int mask(int a, int b) { return (a & b) + 1; }" },
			{ "Java 5 identifiers named yield and when", "void identifiers() { int yield = 1; yield = yield + 1; yield++; int when = yield; }" },

			// Java 7
			{ "Java 7 diamond operator", "java.util.Map<String, java.util.List<Integer>> map = new java.util.HashMap<>();" },
			{ "Java 7 try-with-resources", "void read() throws Exception { try (java.io.Reader r = new java.io.StringReader(\"x\"); final java.io.BufferedReader b = new java.io.BufferedReader(r);) { b.read(); } }" },
			{ "Java 9 try-with-resources on a variable", "void close(java.io.Reader r) throws Exception { try (r) { } catch (java.io.IOException e) { } finally { } }" },
			{ "Java 7 multi-catch", "void multiCatch() { try { } catch (final IllegalStateException | IllegalArgumentException e) { } }" },
			{ "Java 7 binary literal", "int binary = 0b1010;" },
			{ "Java 7 underscores in number literals", "long underscores = 0xFF_FF_FFL + 1_000_000 + 0b1_0;" },
			{ "Java 5 hexadecimal floating point literal", "double hexFloat = 0x1.8p1;" },
			{ "decimal floating point literals with underscores", "double decimals = 1_0.5_0e1_0 + .5 + 1f + 2d;" },

			// Java 8
			{ "Java 8 lambda with one parameter", "java.util.function.Function<Integer, Integer> square = x -> x * x;" },
			{ "Java 8 lambda with parameter list", "java.util.Comparator<String> comparator = (a, b) -> a.compareTo(b);" },
			{ "Java 8 lambda with typed parameters and block", "java.util.function.BiFunction<Integer, Integer, Integer> add = (final Integer x, Integer y) -> { return x + y; };" },
			{ "Java 8 lambda without parameters", "Runnable runnable = () -> System.out.println(\"run\");" },
			{ "Java 8 nested lambda", "java.util.function.Function<Integer, java.util.function.Function<Integer, Integer>> curry = a -> b -> a + b;" },
			{ "Java 8 lambda as argument", "boolean any(java.util.List<String> l) { return l.stream().anyMatch(s -> s.length() > 0 && !s.isEmpty()); }" },
			{ "Java 8 lambda in conditional expression", "Runnable conditional = true ? () -> { } : () -> { };" },
			{ "Java 8 method reference", "void print(java.util.List<String> l) { l.forEach(System.out::println); }" },
			{ "Java 8 constructor reference", "java.util.function.Supplier<java.util.List<String>> supplier = java.util.ArrayList::new;" },
			{ "Java 8 array constructor reference", "java.util.function.IntFunction<int[]> array = int[]::new;" },
			{ "Java 8 method reference on generic type", "java.util.function.Function<java.util.List<String>, Integer> size = java.util.List<String>::size;" },
			{ "Java 8 method references on this and super", "void references() { Runnable a = this::references; java.util.function.Supplier<String> b = super::toString; }" },
			{ "Java 8 cast of a lambda", "Object cast = (Runnable) () -> { };" },
			{ "Java 8 intersection cast", "Object intersection = (Runnable & java.io.Serializable) () -> { };" },

			// Java 10/11
			{ "Java 10 var", "void local() { var list = new java.util.ArrayList<String>(); for (var s : list) { } }" },
			{ "Java 11 var in lambda", "java.util.function.Function<Integer, Integer> varLambda = (var x) -> x;" },

			// Java 14
			{ "Java 14 switch expression with rules", "int rules(int k) { return switch (k) { case 1, 2 -> 3; case 4 -> { yield 5; } default -> throw new IllegalStateException(); }; }" },
			{ "Java 14 switch expression with yield", "int yields(int k) { int r = switch (k) { case 1: yield 10; default: { int yield = 3; yield yield; } }; return r; }" },
			{ "Java 14 switch statement with rules", "void statement(int k) { switch (k) { case 1 -> System.out.println(); default -> { } } }" },
			{ "Java 14 switch expression on constants that look like lambdas", "int constants(java.time.DayOfWeek d) { return switch (d) { case MONDAY -> 1; default -> 0; } + 1; }" },
			{ "Java 7 switch on strings", "void strings(String s) { switch (s) { case \"a\": case \"b\": break; default: } }" },

			// Java 15
			{ "Java 15 text block", "String textBlock = \"\"\"\n    Hello \"World\" \"\"quoted\"\" \\\"\"\" end\n    \"\"\";" },

			// Java 16/21
			{ "Java 16 instanceof pattern", "boolean pattern(Object o) { return o instanceof String s && !s.isEmpty() || o instanceof final Integer i && i > 0; }" },
			{ "Java 21 record pattern in instanceof", "boolean record(Object o) { return o instanceof Point(int x, var y) && x == y; }" },
			{ "Java 21 type patterns and guards in switch", "String patterns(Object o) { return switch (o) { case null -> \"null\"; case String s when s.isEmpty() -> \"empty\"; case String s -> s; default -> \"other\"; }; }" },
			{ "Java 21 record patterns in switch", "String records(Object o) { return switch (o) { case Point(int x, int y) when x > y -> \"a\"; case Point(Point(var a, var b), _) -> \"b\"; default -> \"c\"; }; }" },
			{ "Java 21 patterns in old switch", "void oldSwitch(Object o) { switch (o) { case Integer i when i > 0: break; case null, default: } }" }, });
	}

	private final String member;

	public TJavaParser(String name, String member) {
		this.member = member;
	}

	@Test
	public void parsesMember() throws ParseException {
		final Java15Parser parser = new Java15Parser(new OffsetCharStream(new StringReader("class A {\n\t" + member + "\n}\n")));
		parser.CompilationUnit(false);

		final FSTTerminal node = findMember((FSTNonTerminal) parser.getRoot());
		assertNotNull("no class member found", node);
		assertEquals(member, node.getBody());
	}

	private static FSTTerminal findMember(FSTNonTerminal compilationUnit) {
		for (final FSTNode classNode : compilationUnit.getChildren()) {
			if (classNode instanceof FSTNonTerminal) {
				for (final FSTNode child : ((FSTNonTerminal) classNode).getChildren()) {
					if ((child instanceof FSTTerminal) && (child.getType().equals("MethodDecl") || child.getType().equals("FieldDecl"))) {
						return (FSTTerminal) child;
					}
				}
			}
		}
		return null;
	}
}
