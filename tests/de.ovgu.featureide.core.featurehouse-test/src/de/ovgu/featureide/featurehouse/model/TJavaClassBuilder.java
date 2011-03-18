package de.ovgu.featureide.featurehouse.model;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

public class TJavaClassBuilder {
	private JavaClassBuilder builder = new JavaClassBuilder(null);
	
	// TEST 1
	private String TEST_FIELD_1 = "private static final long[] a+= 1000;"; 
	private String EXPECTED_MODIFIER_FIELD_1 = "private static final"; 
	private String EXPECTED_TYPE_FIELD_1 = "long[]";
	private String EXPECTED_NAME_FIELD_1 = "a";
	
	@Test
	public void FieldTest1() {
		assertEquals(EXPECTED_MODIFIER_FIELD_1, builder.getFields(TEST_FIELD_1).get(0));
		assertEquals(EXPECTED_TYPE_FIELD_1, builder.getFields(TEST_FIELD_1).get(1));
		assertEquals(EXPECTED_NAME_FIELD_1, builder.getFields(TEST_FIELD_1).get(2));
	}

	// TEST 2
	private String TEST_FIELD_2 = "public Hashtable<String, ExampleFileFilter> a,b,c,\r\nd;";
	private String EXPECTED_MODIFIER_FIELD_2 = "public"; 
	private String EXPECTED_TYPE_FIELD_2 = "Hashtable<String,ExampleFileFilter>";
	private String EXPECTED_NAME_FIELD_2_1 = "a";
	private String EXPECTED_NAME_FIELD_2_2 = "b";
	private String EXPECTED_NAME_FIELD_2_3 = "c";
	private String EXPECTED_NAME_FIELD_2_4 = "d";
	
	@Test
	public void FieldTest2() {
		assertEquals(EXPECTED_MODIFIER_FIELD_2, builder.getFields(TEST_FIELD_2).get(0));
		assertEquals(EXPECTED_TYPE_FIELD_2, builder.getFields(TEST_FIELD_2).get(1));
		assertEquals(EXPECTED_NAME_FIELD_2_1, builder.getFields(TEST_FIELD_2).get(2));
		assertEquals(EXPECTED_NAME_FIELD_2_2, builder.getFields(TEST_FIELD_2).get(3));
		assertEquals(EXPECTED_NAME_FIELD_2_3, builder.getFields(TEST_FIELD_2).get(4));
		assertEquals(EXPECTED_NAME_FIELD_2_4, builder.getFields(TEST_FIELD_2).get(5));
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
}
