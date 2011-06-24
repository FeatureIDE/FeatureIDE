package de.ovgu.featureide.featurehouse.model;

import static org.junit.Assert.assertEquals;

import org.junit.Test;


public class TCClassBuilder {
	private CClassBuilder builder = new CClassBuilder(null);
	
	// METHOD TEST 1
	private String TEST_METHOD_1 = "int\nfindUserPublicKeyPair (void *listdata, void *searchdata){\n}"; 
	private String EXPECTED_NAME_METHOD_1 = "findUserPublicKeyPair";
	private String EXPECTED_RETURNTYPE_METHOD_1 = "int";
	private String EXPECTED_MODIFIER_METHOD_1 = ""; 
	private String EXPECTED_PARAMETER_1_METHOD_1 = "void *listdata";
	private String EXPECTED_PARAMETER_2_METHOD_1 = "void *searchdata";
	
	@Test
	public void MethodTest1() {
		assertEquals(EXPECTED_NAME_METHOD_1, builder.getMethod(TEST_METHOD_1).get(0));
		assertEquals(EXPECTED_RETURNTYPE_METHOD_1, builder.getMethod(TEST_METHOD_1).get(1));
		assertEquals(EXPECTED_MODIFIER_METHOD_1, builder.getMethod(TEST_METHOD_1).get(2));
		assertEquals(EXPECTED_PARAMETER_1_METHOD_1, builder.getMethod(TEST_METHOD_1).get(3));
		assertEquals(EXPECTED_PARAMETER_2_METHOD_1, builder.getMethod(TEST_METHOD_1).get(4));
	}
	
	// METHOD TEST 2
	private String TEST_METHOD_2 = "unsigned int uni_int(unsigned int n){}"; 
	private String EXPECTED_NAME_METHOD_2 = "uni_int";
	private String EXPECTED_RETURNTYPE_METHOD_2 = "unsigned int";
	private String EXPECTED_MODIFIER_METHOD_2 = ""; 
	private String EXPECTED_PARAMETER_1_METHOD_2 = "unsigned int n";
	
	@Test
	public void MethodTest2() {
		assertEquals(EXPECTED_NAME_METHOD_2, builder.getMethod(TEST_METHOD_2).get(0));
		assertEquals(EXPECTED_RETURNTYPE_METHOD_2, builder.getMethod(TEST_METHOD_2).get(1));
		assertEquals(EXPECTED_MODIFIER_METHOD_2, builder.getMethod(TEST_METHOD_2).get(2));
		assertEquals(EXPECTED_PARAMETER_1_METHOD_2, builder.getMethod(TEST_METHOD_2).get(3));
	}

	// FIELD TEST 1
	private String TEST_FIELD_1 = "static long tps;"; 
	private String EXPECTED_MODIFIER_FIELD_1 = "static"; 
	private String EXPECTED_TYPE_FIELD_1 = "long";
	private String EXPECTED_NAME_FIELD_1 = "tps";
	
	@Test
	public void FieldTest1() {
		assertEquals(EXPECTED_MODIFIER_FIELD_1, builder.getFields(TEST_FIELD_1).get(0));
		assertEquals(EXPECTED_TYPE_FIELD_1, builder.getFields(TEST_FIELD_1).get(1));
		assertEquals(EXPECTED_NAME_FIELD_1, builder.getFields(TEST_FIELD_1).get(2));
	}
	
	// FIELD TEST 2
	private String TEST_FIELD_2 = "static int a, b , c ;"; 
	private String EXPECTED_MODIFIER_FIELD_2 = "static"; 
	private String EXPECTED_TYPE_FIELD_2 = "int";
	private String EXPECTED_NAME_FIELD_2_1 = "a";
	private String EXPECTED_NAME_FIELD_2_2 = "b";
	private String EXPECTED_NAME_FIELD_2_3 = "c";
	
	@Test
	public void FieldTest2() {
		assertEquals(EXPECTED_MODIFIER_FIELD_2, builder.getFields(TEST_FIELD_2).get(0));
		assertEquals(EXPECTED_TYPE_FIELD_2, builder.getFields(TEST_FIELD_2).get(1));
		assertEquals(EXPECTED_NAME_FIELD_2_1, builder.getFields(TEST_FIELD_2).get(2));
		assertEquals(EXPECTED_NAME_FIELD_2_2, builder.getFields(TEST_FIELD_2).get(3));
		assertEquals(EXPECTED_NAME_FIELD_2_3, builder.getFields(TEST_FIELD_2).get(4));
	}
}
