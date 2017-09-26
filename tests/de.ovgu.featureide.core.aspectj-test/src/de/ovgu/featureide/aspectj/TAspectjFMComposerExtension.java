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
package de.ovgu.featureide.aspectj;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

/**
 * Tests for AspectJ renaming;
 *
 * @author Jens Meinicke
 */
public class TAspectjFMComposerExtension {

	private final AspectJFMCompserExtension fmComposerExtension = new AspectJFMCompserExtension();

	private static final String CONTENT_1 =
		"public aspect Hello{\r\n" + "before(): call(void Main.print()) {\r\n" + "	System.out.print(\"Hello\");\r\n" + "	}\r\n" + "}";
	private static final Object NEW_CONTENT_1 =
		"public aspect NewAspect{\r\n" + "before(): call(void Main.print()) {\r\n" + "	System.out.print(\"Hello\");\r\n" + "	}\r\n" + "}";

	private static final String OLD_NAME_1_1 = "Hello";
	private static final String NEW_NAME_1 = "NewAspect";

	@Test
	public void performRenamingsTest_1_1() {
		assertEquals(fmComposerExtension.changeFileContent(CONTENT_1, OLD_NAME_1_1, NEW_NAME_1, true), NEW_CONTENT_1);
	}

	private static final String OLD_NAME_1_2 = "Hell";

	@Test
	public void performRenamingsTest_1_2() {
		assertEquals(fmComposerExtension.changeFileContent(CONTENT_1, OLD_NAME_1_2, NEW_NAME_1, true), CONTENT_1);
	}

	private static final String CONTENT_2 = "abstract aspect AbstractLogger {\r\n" + "declare precedence: AbstractLogger, PrintLogger, SetLogger;\r\n"
		+ "	abstract pointcut loggingPointcut();\r\n" + "	PrintStream loggingTarget = System.out;\r\n" + "	protected void log(String logStr) {\r\n"
		+ "	loggingTarget.println(logStr);\r\n" + "	}\r\n" + "	after() : loggingPointcut() {\r\n" + "	log('Join point reached ' + thisJoinPoint);\r\n"
		+ "	}\r\n" + "}\r\n" + "aspect PrintLogger extends AbstractLogger {\r\n" + "	pointcut loggingPointcut() : execution(* print*(..));\r\n" + "}\r\n"
		+ "aspect SetLogger extends AbstractLogger {\r\n" + "	pointcut loggingPointcut() : execution(* set*(..));\r\n"
		+ "	protected voidlog(String logStr) {\r\n" + "	super.log('Set Method: ' + logStr);\r\n" + "	}\r\n" + "}";

	private static final String CONTENT_2_1 = "abstract aspect ALogger {\r\n" + "declare precedence: ALogger, PrintLogger, SetLogger;\r\n"
		+ "	abstract pointcut loggingPointcut();\r\n" + "	PrintStream loggingTarget = System.out;\r\n" + "	protected void log(String logStr) {\r\n"
		+ "	loggingTarget.println(logStr);\r\n" + "	}\r\n" + "	after() : loggingPointcut() {\r\n" + "	log('Join point reached ' + thisJoinPoint);\r\n"
		+ "	}\r\n" + "}\r\n" + "aspect PrintLogger extends ALogger {\r\n" + "	pointcut loggingPointcut() : execution(* print*(..));\r\n" + "}\r\n"
		+ "aspect SetLogger extends ALogger {\r\n" + "	pointcut loggingPointcut() : execution(* set*(..));\r\n" + "	protected voidlog(String logStr) {\r\n"
		+ "	super.log('Set Method: ' + logStr);\r\n" + "	}\r\n" + "}";

	private static final String OLD_NAME_2_1 = "AbstractLogger";
	private static final String NEW_NAME_2_1 = "ALogger";

	@Test
	public void performRenamingsTest_2_1() {
		assertEquals(fmComposerExtension.changeFileContent(CONTENT_2, OLD_NAME_2_1, NEW_NAME_2_1, true), CONTENT_2_1);
	}

	private static final String CONTENT_2_2 = "abstract aspect AbstractLogger {\r\n" + "declare precedence: AbstractLogger, PLogger, SetLogger;\r\n"
		+ "	abstract pointcut loggingPointcut();\r\n" + "	PrintStream loggingTarget = System.out;\r\n" + "	protected void log(String logStr) {\r\n"
		+ "	loggingTarget.println(logStr);\r\n" + "	}\r\n" + "	after() : loggingPointcut() {\r\n" + "	log('Join point reached ' + thisJoinPoint);\r\n"
		+ "	}\r\n" + "}\r\n" + "aspect PLogger extends AbstractLogger {\r\n" + "	pointcut loggingPointcut() : execution(* print*(..));\r\n" + "}\r\n"
		+ "aspect SetLogger extends AbstractLogger {\r\n" + "	pointcut loggingPointcut() : execution(* set*(..));\r\n"
		+ "	protected voidlog(String logStr) {\r\n" + "	super.log('Set Method: ' + logStr);\r\n" + "	}\r\n" + "}";

	private static final String OLD_NAME_2_2 = "PrintLogger";
	private static final String NEW_NAME_2_2 = "PLogger";

	@Test
	public void performRenamingsTest_2_2() {
		assertEquals(fmComposerExtension.changeFileContent(CONTENT_2, OLD_NAME_2_2, NEW_NAME_2_2, true), CONTENT_2_2);
	}

	private static final String CONTENT_2_3 = "abstract aspect AbstractLogger {\r\n" + "declare precedence: AbstractLogger, PrintLogger, SLogger;\r\n"
		+ "	abstract pointcut loggingPointcut();\r\n" + "	PrintStream loggingTarget = System.out;\r\n" + "	protected void log(String logStr) {\r\n"
		+ "	loggingTarget.println(logStr);\r\n" + "	}\r\n" + "	after() : loggingPointcut() {\r\n" + "	log('Join point reached ' + thisJoinPoint);\r\n"
		+ "	}\r\n" + "}\r\n" + "aspect PrintLogger extends AbstractLogger {\r\n" + "	pointcut loggingPointcut() : execution(* print*(..));\r\n" + "}\r\n"
		+ "aspect SLogger extends AbstractLogger {\r\n" + "	pointcut loggingPointcut() : execution(* set*(..));\r\n"
		+ "	protected voidlog(String logStr) {\r\n" + "	super.log('Set Method: ' + logStr);\r\n" + "	}\r\n" + "}";

	private static final String OLD_NAME_2_3 = "SetLogger";
	private static final String NEW_NAME_2_3 = "SLogger";

	@Test
	public void performRenamingsTest_2_3() {
		assertEquals(fmComposerExtension.changeFileContent(CONTENT_2, OLD_NAME_2_3, NEW_NAME_2_3, true), CONTENT_2_3);
	}

	private static final String PACKAGE_CONTENT = "/* HEADER */\r\n" + "package P;\r\n" + "public aspect Main {\r\n" + "public Main() {\r\n" + "}\r\n" + "}";

	private static final String OLD_PACKAGE_CONTENT = "/* HEADER */\r\n" + "package P;\r\n" + "public aspect OLD {\r\n" + "public Main() {\r\n" + "}\r\n" + "}";

	private static final String NEW_PACKAGE_CONTENT =
		"/* HEADER */\r\n" + "package P2;\r\n" + "public aspect NEW {\r\n" + "public Main() {\r\n" + "}\r\n" + "}";

	private static final String OLD_NAME_PACKAGE = "OLD";
	private static final String NEW_NAME_PACKAGE = "P2_NEW";

	@Test
	public void performRenamingsPackageTest() {
		assertEquals(PACKAGE_CONTENT, fmComposerExtension.changeFileContent(PACKAGE_CONTENT, OLD_NAME_PACKAGE, NEW_NAME_PACKAGE, false));
	}

	@Test
	public void performRenamingsPackageTest_2() {
		assertEquals(NEW_PACKAGE_CONTENT, fmComposerExtension.changeFileContent(OLD_PACKAGE_CONTENT, OLD_NAME_PACKAGE, NEW_NAME_PACKAGE, true));
	}

	public static void main(String[] args) {
		System.out.println(OLD_PACKAGE_CONTENT.contains("package P;"));
		System.out.println(OLD_PACKAGE_CONTENT.matches("[\\w*,\\W*]*package\\s+\\w*;[\\w,\\W]*"));
		System.out.println(OLD_PACKAGE_CONTENT.matches("[\\w*,\\W*]*packag\\s+\\w*;[\\w,\\W]*"));
	}

}
