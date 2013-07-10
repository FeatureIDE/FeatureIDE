import org.junit.Test; import gov.nasa.jpf.util.test.TestJPF;

public  class StringMatcherTest extends TestJPF {

	@Test
	public void accountMC() {
		if (verifyNoPropertyViolation()) {
			accountTest();
		}
	}
	
	@Test
	public void accountTest() {
		StringMatcher m = new StringMatcher("blabla");
		
		if (!m.match("blaxxx")) {
//				System.out.println(FeatureModel.getSelection(true));
			assertTrue(false);
		}
	}
}
