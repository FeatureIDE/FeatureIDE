package TestSpecifications;

import java.util.HashSet;
import java.util.Set;

import EmailSystem.Client;
import EmailSystem.Email;

public class Specification6 {
	
	private Set<Email> encryptedMails = new HashSet<Email>(2);
	public String getName() {
		return "6-Encrypt-Decrypt";
	}
	
	public void callFromIncoming__role__Decrypt(Email msg, int encryptionKey, int clientPrivateKey) {
		if (encryptedMails.contains(msg)) {
			if (!(Client.isKeyPairValid(encryptionKey, clientPrivateKey))) {
				throw new SpecificationException(getName(), "Received Mail is unreadable because encrypted with old Key (TestCase 6 Error Condition)");
			}
		}
	}
	public void callFromMail(Email msg, boolean isEncrypted) {
		if (isEncrypted) {
			encryptedMails.add(msg);
		}
	}
}
