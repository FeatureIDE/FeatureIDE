package EmailSystem;

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
}
