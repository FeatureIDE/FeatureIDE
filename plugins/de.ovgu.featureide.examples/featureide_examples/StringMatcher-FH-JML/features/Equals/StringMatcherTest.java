import gov.nasa.jpf.util.test.TestJPF;

import org.junit.Test;
//import gov.nasa.jpf.util.test.TestJPF;
import static org.junit.Assert.*;

public class StringMatcherTest extends TestJPF {

	
	public void testCompare() {
	//	if (verifyNoPropertyViolation()) {
		System.out.println("feature equals");
	//		 FeatureModel.equals_ = true;
			// @feature Equals
			String expected = "abc";
			System.out.println("selection:\n "+FeatureModel.getSelection(true)+"\n----");
			assertTrue(StringMatcher.compare("abc", expected));
			assertFalse(StringMatcher.compare("a", expected));
			assertFalse(StringMatcher.compare("b", expected));
			assertFalse(StringMatcher.compare("c", expected));
			assertFalse(StringMatcher.compare("d", expected));
			assertFalse(StringMatcher.compare("ab", expected));
			assertFalse(StringMatcher.compare("ac", expected));
			assertFalse(StringMatcher.compare("ad", expected));
			assertFalse(StringMatcher.compare("abcd", expected));
			assertFalse(StringMatcher.compare("dabc", expected));
			assertFalse(StringMatcher.compare("", expected));

	//	}

	}
}
