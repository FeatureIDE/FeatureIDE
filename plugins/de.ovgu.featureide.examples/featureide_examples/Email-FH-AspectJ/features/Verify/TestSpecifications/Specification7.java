package TestSpecifications;


public class Specification7 {
	public String getName() {
		return "7-Encrypt-Verify";
	}
	
	public void callFromVerify(boolean isReadable) {
		if (!isReadable) {
			throw new SpecificationException(getName(),
					"Email to be verified is not readable (TestCase 7 Error Message)");
		}
	}
}
