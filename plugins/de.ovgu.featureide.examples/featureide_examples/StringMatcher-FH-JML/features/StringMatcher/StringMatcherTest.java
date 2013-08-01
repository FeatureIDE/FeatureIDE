import org.junit.Test; 
//import gov.nasa.jpf.util.test.TestJPF;
import static org.junit.Assert.*;
public  class StringMatcherTest {

	@Test
	public void accountMC() {
	//	if (verifyNoPropertyViolation()) {
			accountTest();
	//	}
	}
	

	public void accountTest() {
		StringMatcher m = new StringMatcher("test");
		
		if (!m.match("text")) {
	//	System.out.println(FeatureModel.getSelection(true));
			//assertTrue(false);
		}
	}
}
