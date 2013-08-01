import org.junit.Test;
//import gov.nasa.jpf.util.test.TestJPF;
import static org.junit.Assert.*;

public  class StringMatcherTest {

	@Test
	public void testContains() {
	//	if (verifyNoPropertyViolation()) {
//			FeatureModel.prefix_a_b_ = true;
		//@Featre Contains
			String expected ="abc";
			
			assertTrue(StringMatcher.contains(expected,"a"));
			assertTrue(StringMatcher.contains(expected,"b"));
			assertTrue(StringMatcher.contains(expected,"c"));
			assertTrue(StringMatcher.contains(expected,"ab"));
			assertTrue(StringMatcher.contains(expected,"bc"));
			assertTrue(StringMatcher.contains(expected,"abc"));
			assertTrue(StringMatcher.contains(expected,""));
			
			assertFalse(StringMatcher.contains(expected,"d"));
			assertFalse(StringMatcher.contains(expected," "));
			assertFalse(StringMatcher.contains(expected,"abcd"));
			assertFalse(StringMatcher.contains(expected,"cd"));
			assertFalse(StringMatcher.contains(expected,"dabc"));
			
			
//				System.out.println(FeatureModel.getSelection(true));
			}
		}
	//}
	

