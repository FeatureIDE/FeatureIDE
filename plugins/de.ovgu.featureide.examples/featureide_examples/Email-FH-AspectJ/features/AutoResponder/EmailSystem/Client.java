package EmailSystem;

public class Client {
	protected boolean autoResponse;
	public void setAutoResponse(boolean autoResponse) {
		this.autoResponse = autoResponse;
	}

	public boolean isAutoResponse() {
		return autoResponse;
	}
	static void autoRespond(Client client, Email msg) {
		Util.prompt("sending autoresponse\n");
		Client sender = msg.getEmailFrom();
		msg.setEmailTo(sender.getName());
		outgoing(client, msg);
		incoming(sender, msg);
	}
	
	// incoming emails are processed by this method before delivery.
	static void incoming(Client client, Email msg) {
		original(client, msg);
		if (client.isAutoResponse()) {
			autoRespond(client, msg);
		}
	}
}
