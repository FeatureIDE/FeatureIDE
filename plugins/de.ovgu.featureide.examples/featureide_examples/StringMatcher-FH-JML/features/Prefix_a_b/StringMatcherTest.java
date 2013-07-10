import org.junit.Test; import gov.nasa.jpf.util.test.TestJPF;

public  class StringMatcherTest extends TestJPF {

	@Test
	public void test2() {
		if (verifyNoPropertyViolation()) {
//			FeatureModel.prefix_a_b_ = true;
			StringMatcher m = new StringMatcher("blabla");
			
			if (!m.match("bla")) {
//				System.out.println(FeatureModel.getSelection(true));
			}
		}
	}
	
}
