/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ahead;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

/**
 * Tests for the <code>Ahead</code> composer.
 * 
 * @author Jens Meinicke
 */
public class TAheadComposer {

	public static final String SOUCE_1 = 
			"layer test;\r\n" + 
			"import import1;\r\n" + 
			"public class test {\r\n" + 
			"private Player player;" + 
			"	private void method1() {\r\n" + 
			"\r\n" + 
			"	}\r\n" + 
			"}";
	private static final String CORRECTED_1 = 
			"\r\n" + 
			"import import1;\r\n" + 
			"public class test {\r\n" + 
			"private Player player;" + 
			"	private void method1() {\r\n" + 
			"\r\n" + 
			"	}\r\n" + 
			"}";

	/**
	 * Tests layer removing.
	 */
	@Test
	public void correctFileTextTest_1() {
		assertEquals(AheadComposer.correctFileText(SOUCE_1), CORRECTED_1);
	}

	private static final String SOUCE_2 = 
			"import import1;\r\n" + 
			"public class test {\r\n" + 
			"	private void method1() {\r\n" + 
			"\r\n" + 
			"	}\r\n" + 
			"}";
	private static final String CORRECTED_2 = 
			"\r\n" + 
			"import import1;\r\n" + 
			"public class test {\r\n" + 
			"	private void method1() {\r\n" + 
			"\r\n" + 
			"	}\r\n" + 
			"}";

	/**
	 * Tests adding a line brake before import;
	 */
	@Test
	public void correctFileTextTest_2() {
		assertEquals(AheadComposer.correctFileText(SOUCE_2), CORRECTED_2);
	}

	private static final String SOUCE_3 = 
			"\r\n" + 
			"import player.*;\r\n" + 
			"public class Player {\r\n" + 
			"	private void player() {\r\n" + 
			"\r\n" + 
			"	}\r\n" + 
			"private Player player;\r\n" + 
			"}";

	/**
	 * Tests ignoring other layer occurrences.
	 */
	@Test
	public void correctFileTextTest_3() {
		assertEquals(AheadComposer.correctFileText(SOUCE_3), null);
	}
}
