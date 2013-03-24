package EmailSystem;

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
}
