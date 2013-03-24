package EmailSystem;

public class Client {
	protected Client forwardReceiver;
	
	public void setForwardReceiver(Client forwardReceiver) {
		this.forwardReceiver = forwardReceiver;
	}

	public Client getForwardReceiver() {
		return forwardReceiver;
	}

	static void forward(Client client, Email msg) {
		Util.prompt("Forwarding message.\n");
		Email.printMail(msg);
		outgoing(client, msg);
	}

	static void incoming(Client client, Email msg) {
		original(client, msg);
		Client receiver = client.getForwardReceiver();
		if (receiver != null) {
			msg.setEmailTo(receiver.getName());
			forward(client, msg);
			incoming(receiver, msg);
		}
	}
}
