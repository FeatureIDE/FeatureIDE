import gov.nasa.jpf.util.test.TestJPF;

import org.junit.Test;
//import gov.nasa.jpf.util.test.TestJPF;
import static org.junit.Assert.*;

public class StringMatcherTest extends TestJPF {

	
	public void testCompare() {
	//	if (verifyNoPropertyViolation()) {
		System.out.println("feature prefix a b");
	//		 FeatureModel.prefix_a_b_ = true;
			// @feature Prefix_a_b
			String expected = "abc";
			System.out.println("selection:\n "+FeatureModel.getSelection(true)+"\n----");
			assertTrue(StringMatcher.compare("a", expected));
			assertTrue(StringMatcher.compare("ab", expected));
			assertTrue(StringMatcher.compare("abc", expected));
			assertTrue(StringMatcher.compare("", expected));
			assertFalse(StringMatcher.compare(" ", expected));
			assertTrue(StringMatcher.compare("d", expected));
			assertFalse(StringMatcher.compare("abcd", expected));
			assertFalse(StringMatcher.compare("abd", expected));
			assertFalse(StringMatcher.compare("ad", expected));
			assertFalse(StringMatcher.compare("dabc", expected));
			assertFalse(StringMatcher.compare("dab", expected));
			assertFalse(StringMatcher.compare("da", expected));

	//	}
	}
}
