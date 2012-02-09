/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ahead.actions;

import static org.junit.Assert.assertEquals;

import java.util.LinkedList;

import org.junit.Test;
/**
 * Test for conversion from <code>Ahead</code> to <code>FeatureHouse</code>.
 * 
 * @author Jens Meinicke
 */
public class TFeatureHouseToAHEADConversion {
	
	private FeatureHouseToAHEADConversion converter = new FeatureHouseToAHEADConversion(null);
	
	private String TEXT_1 = 
			"/r/n" +
			"/r/n" +
			"public class testClass {/r/n" +
			"/r/n" +
			" public void method() {/r/n" +
			"  original();/r/n" +
			" }/r/n" +
			"}";
	
	private String CHANGED_TEXT_1 = 
			"/r/n" +
			"/r/n" +
			"public refines class testClass {/r/n" +
			"/r/n" +
			" public void method() {/r/n" +
			"  Super().method();/r/n" +
			" }/r/n" +
			"}";

	@Test
	public void changeFile_1() {
		LinkedList<String> methodNames = new LinkedList<String>();
		methodNames.add("method");
		assertEquals(CHANGED_TEXT_1, converter.TChangeFile(TEXT_1, methodNames));
	}
	
	private String TEXT_2 = 
			"package testPackage;/r/n" +
			"/r/n" +
			"public class testClass {/r/n" +
			"/r/n" +
			" public void method() {/r/n" +
			"  original();/r/n" +
			" }/r/n" +
			"}";
	
	private String CHANGED_TEXT_2 = 
			"/r/n" +
			"/r/n" +
			"public refines class testClass {/r/n" +
			"/r/n" +
			" public void method() {/r/n" +
			"  Super().method();/r/n" +
			" }/r/n" +
			"}";
	
	@Test
	public void changeFile_2() {
		LinkedList<String> methodNames = new LinkedList<String>();
		methodNames.add("method");
		assertEquals(CHANGED_TEXT_2, converter.TChangeFile(TEXT_2, methodNames));
	}
}
