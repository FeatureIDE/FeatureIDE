import gov.nasa.jpf.util.test.TestJPF;

import org.junit.Test;
//import gov.nasa.jpf.util.test.TestJPF;
import static org.junit.Assert.*;

public class StringMatcherTest extends TestJPF {

	
	public void testCompare() {
		if (verifyNoPropertyViolation()) {
			System.out.println("feature length");
		 FeatureModel.length_ = true;
	
			// @feature Length
			String expected = "abc";
			System.out.println("selection:\n "+FeatureModel.getSelection(true)+"\n----");
			 System.out.println("valid: "+ FeatureModel.valid());
			assertTrue(StringMatcher.compare("abc", expected));
			assertTrue(StringMatcher.compare("abd", expected));
			assertTrue(StringMatcher.compare("dab", expected));

			assertFalse(StringMatcher.compare("a", expected));
			assertFalse(StringMatcher.compare("ab", expected));
			assertFalse(StringMatcher.compare("", expected));
			assertFalse(StringMatcher.compare("d", expected));
			assertFalse(StringMatcher.compare("abcd", expected));
			assertFalse(StringMatcher.compare("ad", expected));
			assertFalse(StringMatcher.compare("dabc", expected));
			assertFalse(StringMatcher.compare("da", expected));
	
		}
	}
}
