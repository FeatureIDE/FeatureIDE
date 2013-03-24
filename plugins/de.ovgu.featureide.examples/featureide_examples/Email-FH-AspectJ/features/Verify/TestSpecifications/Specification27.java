package TestSpecifications;

public class Specification27 {
	
	public String getName() {
		return "27-Verify-Forward";
	}
	
	public void callFromMail(boolean isSignatureVerified) {
		if (isSignatureVerified) {
			throw new SpecificationException(getName(), "Forwarded message still carries signed bit (TestCase 27 Error Condition)");
		}
	}
}
