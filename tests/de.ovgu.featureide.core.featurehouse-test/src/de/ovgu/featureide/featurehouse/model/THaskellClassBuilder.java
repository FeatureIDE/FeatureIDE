package de.ovgu.featureide.featurehouse.model;

import static org.junit.Assert.assertEquals;

import org.junit.Test;


public class THaskellClassBuilder {
	private HaskellClassBuilder builder = new HaskellClassBuilder(null);
	
	// METHOD TEST 1
	private String TEST_METHOD_1 = "mapResult :: (a -> Result b err) -> Result a err -> Result b err"; 
	private String EXPECTED_NAME_METHOD_1 = "mapResult";
	private String EXPECTED_PARAMETER_1_METHOD_1 = "(a -> Result b err) -> Result a err -> Result b err";
	
	@Test
	public void MethodTest1() {
		assertEquals(EXPECTED_NAME_METHOD_1, builder.getMethod(TEST_METHOD_1).get(0));
		assertEquals(EXPECTED_PARAMETER_1_METHOD_1, builder.getMethod(TEST_METHOD_1).get(1));
	}
}
