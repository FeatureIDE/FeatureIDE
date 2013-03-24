package EmailSystem;

public class Client {
	/**
	 * stores an alias to List-of-adresses mapping. (by sending to one alias the
	 * email can be sent to multiple clients ~ mailing-lists?)
	 */
	protected ArrayList<AddressBookEntry> addressbook = new ArrayList<AddressBookEntry>();
	
	/**
	 * Returns the empty list if alias is unknown.
	 */
	public List<String> getAddressBookReceiversForAlias(String alias) {
		for (AddressBookEntry e : addressbook) {
			if (e.getAlias().equals(alias)) {
				return e.getReceivers();
			}
		}
		return Collections.emptyList();
	}
	
	/**
	 * Adds a new receiver to the address book entry identified with alias. If
	 * the entry does not exist it is created.
	 */
	public void addAddressbookEntry(String alias, String receiver) {
		for (AddressBookEntry e : addressbook) {
			if (e.getAlias().equals(alias)) {
				e.addReceiver(receiver);
				return;
			}
		}
		AddressBookEntry newEntry = new AddressBookEntry(alias);
		newEntry.addReceiver(receiver);
		addressbook.add(newEntry);
	}
	


	static void outgoing(Client client, Email msg) {
		List<String> aliasReceivers = client
				.getAddressBookReceiversForAlias(msg.getEmailTo());
		if (!aliasReceivers.isEmpty()) {
			// found alias, sending to the addresses that are associated with
			// this alias (to addresses 1,2,...) address 0 will be handled by the other methods
			for (int i = 1; i < aliasReceivers.size(); i++) {
				String receiverAddress = aliasReceivers.get(i);
				msg.setEmailTo(receiverAddress);
				outgoing(client, msg);
				incoming(Client.getClientByAdress(receiverAddress), msg);
			}
			msg.setEmailTo(aliasReceivers.get(0));
			original(client, msg);
		} else {
			// no alias, must be a normal address
			original(client, msg);
		}
	}

	static class AddressBookEntry {
		String alias;
		ArrayList<String> receivers;

		public AddressBookEntry(String alias) {
			super();
			this.alias = alias;
			this.receivers = new ArrayList<String>();
		}

		public void addReceiver(String address) {
			receivers.add(address);
		}

		public String getAlias() {
			return alias;
		}

		public ArrayList<String> getReceivers() {
			return receivers;
		}
	}
}
