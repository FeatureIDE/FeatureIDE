import java.util.ArrayList;
import java.util.List;

import EmailSystem.Client;
import EmailSystem.Util;
import TestSpecifications.SpecificationManager;

/**
 * This class implements the actions that can be executed by the test scenarios.
 * (setup() is always executed first to setup the characters and their private keys)
 * @author rhein
 */
public class Test_Actions {
	/**
	 * Bob gets Key of RJH
	 */
	static void bobKeyAdd() {
		actionHistory.add("bobKeyAdd");
		// unrealistic simplification. Private key == Public key
		bob.addKeyringEntry(rjh, rjh.getPrivateKey());
		Util.prompt("bob added rjhs key");
	}

	/**
	 * Bob gets Key of Chuck
	 */
	static void bobKeyAddChuck() {
		actionHistory.add("bobKeyAddChuck");
		// unrealistic simplification. Private key == Public key
		bob.addKeyringEntry(chuck, chuck.getPrivateKey());
	}

	static void bobKeyChange() {
		actionHistory.add("bobKeyChange");
		Client.generateKeyPair(bob, 777);
	}

	/**
	 * Chuck gets Key of Bob
	 */
	static void chuckKeyAdd() {
		actionHistory.add("chuckKeyAdd");
		chuck.addKeyringEntry(bob, bob.getPrivateKey());
	}

	/**
	 * Delete RJHs private key
	 */
	static void rjhDeletePrivateKey() {
		actionHistory.add("rjhDeletePrivateKey");
		rjh.setPrivateKey(0);
	}
	
	/**
	 * RJH gets Key of Bob
	 */
	static void rjhKeyAdd() {
		actionHistory.add("rjhKeyAdd");
		rjh.addKeyringEntry(bob, bob.getPrivateKey());
	}

	// actions
	/**
	 * RJH gets Key of Chuck
	 */
	static void rjhKeyAddChuck() {
		actionHistory.add("rjhKeyAddChuck");
		rjh.addKeyringEntry(chuck, chuck.getPrivateKey());
	}

	static void rjhKeyChange() {
		actionHistory.add("rjhKeyChange");
		Client.generateKeyPair(rjh, 666);
	}

	
	static void setup_bob(Client bob) {
		bob.setPrivateKey(123);
	}

	static void setup_chuck(Client chuck) {
		chuck.setPrivateKey(789);
	}

	static void setup_rjh(Client rjh) {
		rjh.setPrivateKey(456);
	}

}
