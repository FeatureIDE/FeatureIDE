package EmailSystem;

import EmailSystem.Email;

public class Client {
	static void incoming(Client client, Email msg) {
		// decrypt

		int privkey = client.getPrivateKey();
		if (privkey != 0) {
			if (msg.isEncrypted()
					&& isKeyPairValid(msg.getEmailEncryptionKey(), privkey)) {
				msg.setEmailIsEncrypted(false);
				msg.setEmailEncryptionKey(0);
			}
		}
		// end decrypt

		original(client, msg);
	}

	/*@
	  @ requires encryptedMails.contains(msg) ==> Client.isKeyPairValid(msg.getEmailEncryptionKey(), client.getPrivateKey());
	  @ assignable \nothing;
	  @*/
	static void incoming(Client client, Email msg) {
		original(client, msg);
	}

}
