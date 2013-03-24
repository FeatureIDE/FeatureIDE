package TestSpecifications;

public class Specification11 {
	
	public String getName() {
		return "11-Decrypt-AutoResponder";
	}
	
	public void callFromAutoRespond(boolean isReadable) {
		if (!isReadable) {
			throw new SpecificationException(getName(), "Mail was not decrypted before AutoRespond (TestCase 11 Error Condition)");
		}
	}
	
	
	
	
	
}
