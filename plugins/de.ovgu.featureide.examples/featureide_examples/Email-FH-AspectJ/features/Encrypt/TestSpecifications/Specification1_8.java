package TestSpecifications;

import java.util.HashSet;
import java.util.Set;
import EmailSystem.Email;

/**
 * This Specification is violated in two Scenarios (1 and 8)
 * @author rhein
 */
public class Specification1_8 {
	
	/**
	 * Stores Emails that have been sent encrypted.
	 * These must never be sent unencrypted again. 
	 */
	private Set<Email> encryptedMails = new HashSet<Email>(2);
	
	/**
	 * Stores Emails that have been sent unEncrypted.
	 * These must never be sent encrypted again.
	 */
	 private Set<Email> unEncryptedMails = new HashSet<Email>(2);
	public String getName() {
		return "1-AddressBook-Encrypt & 8-Encrypt-AutoResponder";
	}
	
	public  void callFromMail(Email msg, boolean isEncrypted) {
		if (encryptedMails.contains(msg)) {
			if (!isEncrypted) {
				throw new SpecificationException(getName(),"Specification 1 & 8 Error");
			}
		} else if (unEncryptedMails.contains(msg)) {
			if (isEncrypted) {
				throw new SpecificationException(getName(),"Specification 1 & 8 Error");
			}
		} else {
			if (isEncrypted) {
				encryptedMails.add(msg);
			} else {
				unEncryptedMails.add(msg);
			}
		}
	}
}
