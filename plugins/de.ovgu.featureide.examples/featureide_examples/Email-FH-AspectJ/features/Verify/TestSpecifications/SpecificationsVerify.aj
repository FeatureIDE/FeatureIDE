package TestSpecifications;

import EmailSystem.Client;
import EmailSystem.Email;

privileged public aspect SpecificationsVerify {
	 before(Client client, Email msg) : 
		 call(static void EmailSystem.Client.verify(Client, Email)) 
		 && args(client, msg) {
		 // verify
			if (SpecificationManager.checkSpecification(7) && SpecificationManager.spec7 != null) {
				SpecificationManager.spec7.callFromVerify(msg.isReadable());
			}
	}
	 before(Client client, Email msg) : 
		 call(static void EmailSystem.Client.mail(Client, Email)) 
		 && args(client, msg) {
		 // verify
			if (SpecificationManager.checkSpecification(27) && SpecificationManager.spec27 != null) {
				SpecificationManager.spec27.callFromMail(msg.isSignatureVerified());
			}
	}
}