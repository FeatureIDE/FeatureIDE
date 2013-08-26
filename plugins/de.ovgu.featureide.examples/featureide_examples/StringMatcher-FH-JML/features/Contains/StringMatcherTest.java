import org.junit.Test;
//import gov.nasa.jpf.util.test.TestJPF;
import static org.junit.Assert.*;
import gov.nasa.jpf.jvm.Verify;
public  class StringMatcherTest extends TestJPF{
	@Test
	public void accountMC() {
		if (verifyNoPropertyViolation()) {
		FeatureModel.comparison_ =  Verify.getBoolean();
		FeatureModel.contains_ =  Verify.getBoolean();
		FeatureModel.equals_ = Verify.getBoolean();
		FeatureModel.length_ =  Verify.getBoolean();
		FeatureModel.prefix_a_b_ =  Verify.getBoolean();
		FeatureModel.prefix_b_a_ =  Verify.getBoolean();
		FeatureModel.stringmatcher_ = Verify.getBoolean();
		FeatureModel.substring_a_b_ = Verify.getBoolean();
		FeatureModel.substring_b_a_ =  Verify.getBoolean();
		
			
		
		if(FeatureModel.valid())testCompare();
		}
	}
	
	public void testContains() {
	//if (verifyNoPropertyViolation()) {
		
		//@ Featre Contains
			String expected ="abc";
			System.out.println("selection:\n "+FeatureModel.getSelection(true)+"\n----");
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
			
			
			System.out.println(FeatureModel.getSelection(true));
	//		}
		}
	}
	

