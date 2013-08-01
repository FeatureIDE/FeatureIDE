import org.junit.Test;
//import gov.nasa.jpf.util.test.TestJPF;
import static org.junit.Assert.*;

public  class StringMatcherTest {

	@Test
	public void testCompare() {
	//	if (verifyNoPropertyViolation()) {
//			FeatureModel.prefix_a_b_ = true;
		//@feature Substring_a_b
			String expected ="abc";
			
			assertTrue(StringMatcher.compare("a", expected));
			assertTrue(StringMatcher.compare("ab", expected));
			assertTrue(StringMatcher.compare("abc", expected));
			assertTrue(StringMatcher.compare("", expected));
			assertFalse(StringMatcher.compare(" ", expected));
			assertFalse(StringMatcher.compare("d", expected));
			assertFalse(StringMatcher.compare("abcd", expected));
			assertFalse(StringMatcher.compare("abd", expected));
			assertFalse(StringMatcher.compare("ad", expected));
			assertFalse(StringMatcher.compare("dabc", expected));
			assertFalse(StringMatcher.compare("dab", expected));
			assertFalse(StringMatcher.compare("da", expected));

			
}
}
