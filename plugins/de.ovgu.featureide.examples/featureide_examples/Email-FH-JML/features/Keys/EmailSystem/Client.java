package EmailSystem;

public class Client {
	/**
	 * Saves public keys of other clients
	 */
	protected ArrayList<KeyringEntry> keyring = new ArrayList<KeyringEntry>();

	protected int privateKey;

	public void setPrivateKey(int privateKey) {
		this.privateKey = privateKey;
	}

	public /*@pure@*/ int getPrivateKey() {
		return privateKey;
	}

	/**
	 * Currently this method does only set the private key to seed
	 */
	public static void generateKeyPair(Client client, int seed) {
		client.setPrivateKey(seed);
	}

	public void addKeyringEntry(Client client, int publicKey) {
		this.keyring.add(new KeyringEntry(client, publicKey));
	}
	
	/**
	 * Returns the public key of client, if it is saved in this keyring. If not
	 * the method returns 0.
	 */
	public /*@pure@*/ int getKeyringPublicKeyByClient(Client client) {
		for (KeyringEntry e : keyring) {
			if (e.getKeyOwner().equals(client)) {
				return e.getPublicKey();
			}
		}
		return 0;
	}

	public /*@pure@*/  static boolean isKeyPairValid(int publicKey, int privateKey) {
		Util.prompt("keypair valid " + publicKey + " " + privateKey);
		if (publicKey == 0 || privateKey == 0)
			return false;
		return privateKey == publicKey;
	}
	

	static class KeyringEntry {
		private Client keyOwner;
		private int publicKey;

		public KeyringEntry(Client keyOwner, int publicKey) {
			super();
			this.keyOwner = keyOwner;
			this.publicKey = publicKey;
		}

		public Client getKeyOwner() {
			return keyOwner;
		}

		public int getPublicKey() {
			return publicKey;
		}
	}
}
