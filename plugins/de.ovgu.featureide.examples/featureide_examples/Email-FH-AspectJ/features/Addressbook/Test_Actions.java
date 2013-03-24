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
	static void bobSetAddressBook() {
		actionHistory.add("bobSetAddressBook");
		bob.addAddressbookEntry("AliasForRJHandChuck", rjh.getName());
		bob.addAddressbookEntry("AliasForRJHandChuck", chuck.getName());
	}
	static void bobToAlias() {
		if (bob.getAddressBookReceiversForAlias("AliasForRJHandChuck").isEmpty()) {
			actionHistory.add("AbortedBobToAlias");
			return;
		}
		actionHistory.add("bobToAlias");
		String subject = "Subject";
		String body = "Body";
		Client.sendEmail(bob, "AliasForRJHandChuck", subject, body);
	}
}
