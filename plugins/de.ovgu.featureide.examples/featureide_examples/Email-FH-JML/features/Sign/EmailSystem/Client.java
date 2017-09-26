package EmailSystem;

import java.util.HashSet;
import java.util.Set;

import EmailSystem.Client;
import EmailSystem.Email;

public class Client {
	static void outgoing(Client client, Email msg) {
		sign(client, msg);
		original(client, msg);
	}
	/** adds the sign flag to message body
	 */
	static void sign(Client client, Email msg) {
		int privkey = client.getPrivateKey();
		if (privkey == 0)
			return;
		msg.setEmailIsSigned(true);
		msg.setEmailSignKey(privkey);
	}
	
	/*@ model Set<Email> signedMails = new HashSet<Email>(2); @*/

	/*@ \conjunctive_contract
	  @ requires signedMails.contains(msg) ==> Client.isKeyPairValid(client.getKeyringPublicKeyByClient(msg.getEmailFrom()), msg.getEmailSignKey());
	  @ requires msg.isSigned() ==> !Client.isKeyPairValid(client.getKeyringPublicKeyByClient(msg.getEmailFrom()), msg.getEmailSignKey());
	  @ assignable \nothing;
	  @*/
	static void verify(Client client, Email msg) {
		original(client, msg);
	}
	
	/*@ ensures msg.isSigned() ==> signedMails.contains(msg);
	  @ assignable \nothing;
	  @*/
	static void mail(Client client, Email msg) {
		//TODO add to signedMails if msg.isSigned()
		original(client, msg);
	}


}
