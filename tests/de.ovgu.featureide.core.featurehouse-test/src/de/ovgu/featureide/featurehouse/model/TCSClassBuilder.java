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
package de.ovgu.featureide.featurehouse.model;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

/**
 * Test for {@link FeatureHouseModelBuilder} of CSharp files.
 * 
 * @author Jens Meinicke
 */
public class TCSClassBuilder {
	private JavaClassBuilder builder = new JavaClassBuilder(null);
	
	// TEST 1
	private String TEST_FIELD_1 = "List<Node> nodes = new List<Node>();"; 
	private String EXPECTED_MODIFIER_FIELD_1 = ""; 
	private String EXPECTED_TYPE_FIELD_1 = "List<Node>";
	private String EXPECTED_NAME_FIELD_1 = "nodes";
	
	@Test
	public void FieldTest1() {
		assertEquals(EXPECTED_MODIFIER_FIELD_1, builder.getFields(TEST_FIELD_1).get(0));
		assertEquals(EXPECTED_TYPE_FIELD_1, builder.getFields(TEST_FIELD_1).get(1));
		assertEquals(EXPECTED_NAME_FIELD_1, builder.getFields(TEST_FIELD_1).get(2));
	}

	// TEST 2
	private String TEST_FIELD_2 = "public Node a, b;";
	private String EXPECTED_MODIFIER_FIELD_2 = "public"; 
	private String EXPECTED_TYPE_FIELD_2 = "Node";
	private String EXPECTED_NAME_FIELD_2_1 = "a";
	private String EXPECTED_NAME_FIELD_2_2 = "b";
	
	@Test
	public void FieldTest2() {
		assertEquals(EXPECTED_MODIFIER_FIELD_2, builder.getFields(TEST_FIELD_2).get(0));
		assertEquals(EXPECTED_TYPE_FIELD_2, builder.getFields(TEST_FIELD_2).get(1));
		assertEquals(EXPECTED_NAME_FIELD_2_1, builder.getFields(TEST_FIELD_2).get(2));
		assertEquals(EXPECTED_NAME_FIELD_2_2, builder.getFields(TEST_FIELD_2).get(3));
	}
	
	// TEST 3
	private String TEST_FIELD_3 = "int int;";
	private String EXPECTED_MODIFIER_FIELD_3 = ""; 
	private String EXPECTED_TYPE_FIELD_3 = "int";
	private String EXPECTED_NAME_FIELD_3 = "int";	
	
	@Test
	public void FieldTestModifiers3() {
		assertEquals(EXPECTED_MODIFIER_FIELD_3, builder.getFields(TEST_FIELD_3).get(0));
		assertEquals(EXPECTED_TYPE_FIELD_3, builder.getFields(TEST_FIELD_3).get(1));
		assertEquals(EXPECTED_NAME_FIELD_3, builder.getFields(TEST_FIELD_3).get(2));
	}
	
	// Test 4
	private String TEST_FIELD_4 = "protected /*@ spec_public @*/ HashSet nodeSet;";
	private String EXPECTED_MODIFIER_FIELD_4 = "protected"; 
	private String EXPECTED_TYPE_FIELD_4 = "HashSet";
	private String EXPECTED_NAME_FIELD_4 = "nodeSet";

	@Test
	public void FieldTestModifiers4() {
		assertEquals(EXPECTED_MODIFIER_FIELD_4, builder.getFields(TEST_FIELD_4).get(0));
		assertEquals(EXPECTED_TYPE_FIELD_4, builder.getFields(TEST_FIELD_4).get(1));
		assertEquals(EXPECTED_NAME_FIELD_4, builder.getFields(TEST_FIELD_4).get(2));
	}
}
