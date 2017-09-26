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
package de.ovgu.featureide.featurehouse.model;

import static org.junit.Assert.assertEquals;

import java.util.LinkedList;

import org.junit.Test;

/**
 * Test for {@link FeatureHouseModelBuilder} of Java files.
 *
 * @see JavaClassBuilder
 * @author Jens Meinicke
 */
public class TJavaClassBuilder {

	private final JavaClassBuilder builder = new JavaClassBuilder(null);

	// TEST 1
	private final String TEST_FIELD_1 = "private static final long[] a+= 1000;";
	private final String EXPECTED_MODIFIER_FIELD_1 = "private static final";
	private final String EXPECTED_TYPE_FIELD_1 = "long[]";
	private final String EXPECTED_NAME_FIELD_1 = "a";

	@Test
	public void FieldTest1() {
		final LinkedList<String> fields = builder.getFields(TEST_FIELD_1);
		assertEquals(EXPECTED_MODIFIER_FIELD_1, fields.get(0));
		assertEquals(EXPECTED_TYPE_FIELD_1, fields.get(1));
		assertEquals(EXPECTED_NAME_FIELD_1, fields.get(2));
	}

	// TEST 2
	private final String TEST_FIELD_2 = "public Hashtable<String, ExampleFileFilter> a,b,c,\r\nd;";
	private final String EXPECTED_MODIFIER_FIELD_2 = "public";
	private final String EXPECTED_TYPE_FIELD_2 = "Hashtable<String,ExampleFileFilter>";
	private final String EXPECTED_NAME_FIELD_2_1 = "a";
	private final String EXPECTED_NAME_FIELD_2_2 = "b";
	private final String EXPECTED_NAME_FIELD_2_3 = "c";
	private final String EXPECTED_NAME_FIELD_2_4 = "d";

	@Test
	public void FieldTest2() {
		final LinkedList<String> fields = builder.getFields(TEST_FIELD_2);
		assertEquals(EXPECTED_MODIFIER_FIELD_2, fields.get(0));
		assertEquals(EXPECTED_TYPE_FIELD_2, fields.get(1));
		assertEquals(EXPECTED_NAME_FIELD_2_1, fields.get(2));
		assertEquals(EXPECTED_NAME_FIELD_2_2, fields.get(3));
		assertEquals(EXPECTED_NAME_FIELD_2_3, fields.get(4));
		assertEquals(EXPECTED_NAME_FIELD_2_4, fields.get(5));
	}

	// TEST 3
	private final String TEST_FIELD_3 = "int int;";
	private final String EXPECTED_MODIFIER_FIELD_3 = "";
	private final String EXPECTED_TYPE_FIELD_3 = "int";
	private final String EXPECTED_NAME_FIELD_3 = "int";

	@Test
	public void FieldTestModifiers3() {
		final LinkedList<String> fields = builder.getFields(TEST_FIELD_3);
		assertEquals(EXPECTED_MODIFIER_FIELD_3, fields.get(0));
		assertEquals(EXPECTED_TYPE_FIELD_3, fields.get(1));
		assertEquals(EXPECTED_NAME_FIELD_3, fields.get(2));
	}

	// Test 4
	private final String TEST_FIELD_4 = "protected /*@ spec_public @*/ HashSet nodeSet;";
	private final String EXPECTED_MODIFIER_FIELD_4 = "protected";
	private final String EXPECTED_TYPE_FIELD_4 = "HashSet";
	private final String EXPECTED_NAME_FIELD_4 = "nodeSet";

	@Test
	public void FieldTestModifiers4() {
		final LinkedList<String> fields = builder.getFields(TEST_FIELD_4);
		assertEquals(EXPECTED_MODIFIER_FIELD_4, fields.get(0));
		assertEquals(EXPECTED_TYPE_FIELD_4, fields.get(1));
		assertEquals(EXPECTED_NAME_FIELD_4, fields.get(2));
	}

	// Test 5
	private final String METHOD_1 = "private void a() {\r\n\t}";
	private final String METHOD_NAME_1 = "a";
	private final String EXPECTED_HEAD_1 = "private void ";

	@Test
	public void MethodTestGetBody1() {
		assertEquals(EXPECTED_HEAD_1, builder.getHead(METHOD_1, METHOD_NAME_1));
	}

	// Test 6
	private final String METHOD_2 = "private void display () {\r\n\t}";
	private final String METHOD_NAME_2 = "display";
	private final String EXPECTED_HEAD_2 = "private void ";

	@Test
	public void MethodTestGetBody2() {
		assertEquals(EXPECTED_HEAD_2, builder.getHead(METHOD_2, METHOD_NAME_2));
	}

	// Test 7
	private final String METHOD_3 = "@Deprecated\r\nprivate void a() {\r\n\t}";
	private final String METHOD_NAME_3 = "a";
	private final String EXPECTED_HEAD_3 = "private void ";

	@Test
	public void MethodTestGetBody3() {
		assertEquals(EXPECTED_HEAD_3, builder.getHead(METHOD_3, METHOD_NAME_3));
	}

	// Test 8
	private final String TEST_FIELD_8 = "/*@spec_public@*/ private String text;";
	private final String EXPECTED_MODIFIER_FIELD_8 = "private";
	private final String EXPECTED_TYPE_FIELD_8 = "String";
	private final String EXPECTED_NAME_FIELD_8 = "text";

	@Test
	public void FieldTestModifiers8() {
		final LinkedList<String> fields = builder.getFields(TEST_FIELD_8);
		assertEquals(EXPECTED_MODIFIER_FIELD_8, fields.get(0));
		assertEquals(EXPECTED_TYPE_FIELD_8, fields.get(1));
		assertEquals(EXPECTED_NAME_FIELD_8, fields.get(2));
	}

}
