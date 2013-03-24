package TestSpecifications;

import EmailSystem.Client;
import EmailSystem.Email;

privileged public aspect SpecificationsAutoResponder {
	before(Client client, Email msg) : 
		 call(static void EmailSystem.Client.autoRespond(Client, Email)) 
		 && args(client, msg) {
		// autoResponder
		 if (SpecificationManager.checkSpecification(11) && SpecificationManager.spec11 != null) {
				SpecificationManager.spec11.callFromAutoRespond(msg.isReadable());
			}
	}
}