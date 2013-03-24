package TestSpecifications;

import java.util.HashSet;
import java.util.Set;

import EmailSystem.Client;
import EmailSystem.Email;

public class Specification3 {
	
	private Set<Email> signedMails = new HashSet<Email>(2);
	public String getName() {
		return "3-Sign-Verify";
	}
	
	public void callFromMail(Email msg, boolean isSigned) {
		if (isSigned) {
			signedMails.add(msg);
		}
	}
	public void callFromVerify(Email msg, int msgSignKey, int bobPubKey_Old) {
		if (signedMails.contains(msg)) {
			if (!(Client.isKeyPairValid(bobPubKey_Old, msgSignKey))) {
				throw new SpecificationException(getName(), "Email signed with old key (Testcase 3 Error)");
			}
		}
	}
}
