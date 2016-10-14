//import gov.nasa.jpf.annotation.FilterField;

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
	public static boolean executedUnimplementedAction = false;
	static Client bob, rjh, chuck;
	/* Filterfield is possible here. 
	 * It causes some speedup, but no advantage for family, or product based verification.
	 * It might cause more problems than it helps.
	 */ 
	//@FilterField
	public static List<String> actionHistory = new ArrayList<String>();

	/**
	 * Bob gets Key of RJH
	 */
	static void bobKeyAdd() {
		actionHistory.add("bobKeyAdd_NOTIMPL");
		executedUnimplementedAction = true;
	}

	/**
	 * Bob gets Key of Chuck
	 */
	static void bobKeyAddChuck() {
		actionHistory.add("bobKeyAddChuck_NOTIMPL");
		executedUnimplementedAction = true;
	}

	static void bobKeyChange() {
		actionHistory.add("bobKeyChange_NOTIMPL");
		executedUnimplementedAction = true;
	}

	static void bobSetAddressBook() {
		actionHistory.add("bobSetAddressBook_NOTIMPL");
		executedUnimplementedAction = true;
	}

	static void bobToAlias() {
		actionHistory.add("bobToAlias");
		executedUnimplementedAction = true;
	}

	static void bobToRjh() {
		
		actionHistory.add("bobToRjh");
		String subject = "Subject";
		String body = "Body";
		Client.sendEmail(bob, rjh.getName(), subject, body);
	}

	/**
	 * Chuck gets Key of Bob
	 */
	static void chuckKeyAdd() {
		actionHistory.add("chuckKeyAdd_NOTIMPL");
		executedUnimplementedAction = true;
	}

	/**
	 * Delete RJHs private key
	 */
	static void rjhDeletePrivateKey() {
		actionHistory.add("rjhDeletePrivateKey_NOTIMPL");
		executedUnimplementedAction = true;
	}

	static void rjhEnableForwarding() {
		actionHistory.add("rjhEnableForwarding_NOTIMPL");
		executedUnimplementedAction = true;
	}

	/**
	 * RJH gets Key of Bob
	 */
	static void rjhKeyAdd() {
		actionHistory.add("rjhKeyAdd_NOTIMPL");
		executedUnimplementedAction = true;
	}

	// actions
	/**
	 * RJH gets Key of Chuck
	 */
	static void rjhKeyAddChuck() {
		actionHistory.add("rjhKeyAddChuck_NOTIMPL");
		executedUnimplementedAction = true;
	}

	static void rjhKeyChange() {
		actionHistory.add("rjhKeyChange_NOTIMPL");
		executedUnimplementedAction = true;
	}

	static void rjhSetAutoRespond() {
		actionHistory.add("rjhSetAutoRespond_NOTIMPL");
		executedUnimplementedAction = true;
	}

	static void rjhToBob() {
		actionHistory.add("rjhToBob");
		String subject = "subject";
		String body = "body";
		Client.sendEmail(rjh, bob.getName(), subject, body);
	}

	static void setup() {
		actionHistory .add("setup");
		SpecificationManager.setupSpecifications();
		Client.resetClients();

		bob = Client.createClient("bob");
		setup_bob(bob);
		Util.prompt("bob: " + bob.getName() + "(ID: " + bob.getId() + ")");
		// rjh = createClient("rjh");
		rjh = Client.createClient("rjh");
		setup_rjh(rjh);
		Util.prompt("rjh: " + rjh.getName() + "(ID: " + rjh.getId() + ")");
		// chuck = createClient("chuck");
		chuck = Client.createClient("chuck");
		setup_chuck(chuck);
		Util
				.prompt("chuck: " + chuck.getName() + "(ID: " + chuck.getId()
						+ ")");
	}
	static void setup_bob(Client bob) {
	}

	static void setup_chuck(Client chuck) {
	}

	static void setup_rjh(Client rjh) {
	}

}
