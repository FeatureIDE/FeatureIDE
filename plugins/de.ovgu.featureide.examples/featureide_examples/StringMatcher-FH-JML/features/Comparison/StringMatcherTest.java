import org.junit.Test;
import gov.nasa.jpf.util.test.TestJPF;
import static org.junit.Assert.*;
import gov.nasa.jpf.vm.Verify;

public  class StringMatcherTest extends TestJPF{

	@Test
	public void accountMC() {
		if (verifyNoPropertyViolation()) {
			StringMatcher matcher = new StringMatcher("abc");
			matcher.compare("abc", "b");
		}
	}

}
	

