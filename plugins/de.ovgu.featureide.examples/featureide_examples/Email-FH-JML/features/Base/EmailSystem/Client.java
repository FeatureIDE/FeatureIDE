package EmailSystem;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * This class holds the Client information and the email management (sendMail, incoming, outgoing,...)
 * @author rhein
 */
public class Client {
	protected int id;
	protected String name; // name does also serve as address at the moment

	public int getId() {
		return id;
	}
	
	// incoming emails reach the user at this point. here they are put in a
	// mailbox.
	static void deliver(Client client, Email msg) {
		Util.prompt("mail delivered\n");
	}

	// incoming emails are processed by this method before delivery.
	static void incoming(Client client, Email msg) {
		deliver(client, msg);
	}

	// outgoing emails leave the client at this point. here they are put in an
	// outgoing queue instead.
	static void mail(Client client, Email msg) {
		Util.prompt("mail sent");
	}


	// emails to be sent are processed by this method before beeing mailed.
	static void outgoing(Client client, Email msg) {
		msg.setEmailFrom(client);
		mail(client, msg);
	}

	public static int sendEmail(Client sender, String receiverAddress,
			String subject, String body) {
		Email email = Email.createEmail(sender, receiverAddress, subject, body);
		Util.prompt("sending Mail " + email.getId());
		outgoing(sender, email);
		Client receiver = Client.getClientByAdress(email.getEmailTo());
		if (receiver != null) {
			incoming(receiver, email);
		} else {
			throw new IllegalArgumentException("Receiver " + receiverAddress + " Unknown");
		}
		return 0; // die Zeile kommt von mir
	}

	private Client(int id, String name) {
		this.id = id;
		this.name = name;
	}

	public String getName() {
		return name;
	}

	static int clientCounter = 1;

	public static Client createClient(String name) {
		Client client = new Client(clientCounter++, name);
		clients[client.getId()] = client;
		return client;
	}

	static Client[] clients = new Client[4];

	static Client getClientById(int id) {
		return clients[id];
	}

	/**
	 * address equals name for now
	 * 
	 * This method implements the EmailAddress to Receiver lookup. The method
	 * returns null if the address is not found!
	 */
	static Client getClientByAdress(String address) {
		for (int i = 0; i < clients.length; i++) {
			if (clients[i] != null && clients[i].getName().equals(address)) {
				return clients[i];
			}
		}
		return null;
	}

	public static void resetClients() {
		clientCounter = 1;
		for (int i = 0; i < clients.length; i++) {
			clients[i] = null;
		}
	}

	@Override
	public String toString() {
		return name;
	}
}
