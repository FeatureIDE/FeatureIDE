package EmailSystem;

import java.util.HashSet;
import java.util.Set;

import EmailSystem.Client;
import EmailSystem.Email;

public class Client {
	// emails to be sent are processed by this method before being mailed.
	static void outgoing(Client client, Email msg) {

		// encrypt
		Client receiver = getClientByAdress(msg.getEmailTo());
		int pubkey = client.getKeyringPublicKeyByClient(receiver);
		if (pubkey != 0) {
			msg.setEmailEncryptionKey(pubkey);
			msg.setEmailIsEncrypted(true);
			Util.prompt("Encrypted Mail " + msg.getId());
		}
		// msg.setEmailIsEncrypted(true); // von mir gelöscht, das macht keinen
		// sinn!

		// end encrypt

		original(client, msg);
	}
	
	/**
	 * Stores Emails that have been sent encrypted.
	 * These must never be sent unencrypted again. 
	 */
	/*@ model Set<Email> encryptedMails = new HashSet<Email>(2); @*/

	/**
	 * Stores Emails that have been sent unEncrypted.
	 * These must never be sent encrypted again.
	 */
	 /*@ model Set<Email> unEncryptedMails = new HashSet<Email>(2); @*/

	/*@ \conjunctive_contract
	  @ requires msg.isEncrypted() ==> !unEncryptedMails.contains(msg);
	  @ requires !msg.isEncrypted() ==> !encryptedMails.contains(msg);
	  @ requires encryptedMails.contains(msg) ==> msg.isEncrypted();
	  @ ensures msg.isEncrypted() ==> encryptedMails.contains(msg);
	  @ ensures !msg.isEncrypted() ==> unEncryptedMails.contains(msg);
	  @ assignable \nothing;
	  @*/
	static void mail(Client client, Email msg) {
		//TODO add to encryptedMails if msg.isEncrypted(), else to unEncryptedMails
		original(client, msg);
	}
	
	/*@
	  @ ensures msg.isEncrypted() ==> encryptedMails.contains(msg);
	  @ assignable \nothing;
	  @*/
	static void incoming(Client client, Email msg) {
		//TODO add to encryptedMails if msg.isEncrypted()
		original(client, msg);
	}

}
