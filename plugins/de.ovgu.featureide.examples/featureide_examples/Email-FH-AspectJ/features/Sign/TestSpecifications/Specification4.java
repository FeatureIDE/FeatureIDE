package TestSpecifications;

import EmailSystem.Client;

public class Specification4 {
	public String getName() {
		return "4-Sign-Forward";
	}
	
	public void callFromVerify(boolean isSigned, int msgSignKey, int senderKey) {
		if (isSigned) {
			if (Client.isKeyPairValid(senderKey, msgSignKey)) {
				throw new SpecificationException(getName(),
						"Cannot verify Mail because the signKey does not match the senderkey (TestCase 4 Error Condition)");
			}
		}
	}
}
