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
package de.ovgu.featureide.ahead.actions;

import static org.junit.Assert.assertEquals;

import java.util.LinkedList;

import org.junit.Test;

import de.ovgu.featureide.core.conversion.ahead_featurehouse.actions.FeatureHouseToAHEADConversion;

/**
 * Test for conversion from <code>Ahead</code> to <code>FeatureHouse</code>.
 *
 * @author Jens Meinicke
 */
public class TFeatureHouseToAHEADConversion {

	private final FeatureHouseToAHEADConversion converter = new FeatureHouseToAHEADConversion(null);

	private final String TEXT_1 =
		"/r/n" + "/r/n" + "public class testClass {/r/n" + "/r/n" + " public void method() {/r/n" + "  original();/r/n" + " }/r/n" + "}";

	private final String CHANGED_TEXT_1 =
		"/r/n" + "/r/n" + "public refines class testClass {/r/n" + "/r/n" + " public void method() {/r/n" + "  Super().method();/r/n" + " }/r/n" + "}";

	@Test
	public void changeFile_1() {
		final LinkedList<String> methodNames = new LinkedList<String>();
		methodNames.add("method");
		assertEquals(CHANGED_TEXT_1, converter.TChangeFile(TEXT_1, methodNames));
	}

	private final String TEXT_2 =
		"package testPackage;/r/n" + "/r/n" + "public class testClass {/r/n" + "/r/n" + " public void method() {/r/n" + "  original();/r/n" + " }/r/n" + "}";

	private final String CHANGED_TEXT_2 =
		"/r/n" + "/r/n" + "public refines class testClass {/r/n" + "/r/n" + " public void method() {/r/n" + "  Super().method();/r/n" + " }/r/n" + "}";

	@Test
	public void changeFile_2() {
		final LinkedList<String> methodNames = new LinkedList<String>();
		methodNames.add("method");
		assertEquals(CHANGED_TEXT_2, converter.TChangeFile(TEXT_2, methodNames));
	}
}
