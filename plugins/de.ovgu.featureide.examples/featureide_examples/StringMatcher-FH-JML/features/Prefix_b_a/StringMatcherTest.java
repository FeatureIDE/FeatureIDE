import gov.nasa.jpf.util.test.TestJPF;

import org.junit.Test;
//import gov.nasa.jpf.util.test.TestJPF;
import static org.junit.Assert.*;

public class StringMatcherTest extends TestJPF {

	
	public void testCompare() {
		System.out.println("feature prefix b a");
	//	if (verifyNoPropertyViolation()) {
		//	 FeatureModel.prefix_b_a_ = true;
			// @feature Prefix_b_a
			String expected = "abc";
			System.out.println("selection:\n "+FeatureModel.getSelection(true)+"\n----");
			assertTrue(StringMatcher.compare(expected, "a"));
			assertTrue(StringMatcher.compare(expected, "ab"));
			assertTrue(StringMatcher.compare(expected, "abc"));
			assertTrue(StringMatcher.compare(expected, ""));
			assertFalse(StringMatcher.compare(expected, " "));
			assertFalse(StringMatcher.compare(expected, "d"));
			assertFalse(StringMatcher.compare(expected, "abcd"));
			assertFalse(StringMatcher.compare(expected, "abd"));
			assertFalse(StringMatcher.compare(expected, "ad"));
			assertFalse(StringMatcher.compare(expected, "dabc"));
			assertFalse(StringMatcher.compare(expected, "dab"));
			assertFalse(StringMatcher.compare(expected, "da"));

	//	}
	}
}
