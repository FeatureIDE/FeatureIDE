package TestSpecifications;

import EmailSystem.Client;
import EmailSystem.Email;

privileged public aspect SpecificationsSign {
	 before(Client client, Email msg) : 
		 call(static void EmailSystem.Client.verify(Client, Email)) 
		 && args(client, msg) {
		 // sign
		if (SpecificationManager.checkSpecification(3) && SpecificationManager.spec3 != null) {
			int bobsOldKey = client.getKeyringPublicKeyByClient(msg.getEmailFrom());
			SpecificationManager.spec3.callFromVerify(msg, msg.getEmailSignKey(), bobsOldKey);
		}
		if (SpecificationManager.checkSpecification(4) && SpecificationManager.spec4 != null) {
			int senderKey = client.getKeyringPublicKeyByClient(msg.getEmailFrom());
			SpecificationManager.spec4.callFromVerify(msg.isSigned(), senderKey, msg.getEmailSignKey());
		}
	}
	before(Client client, Email msg) : 
		 call(static void EmailSystem.Client.mail(Client, Email)) 
		 && args(client, msg) {
		 // sign
		 if (SpecificationManager.checkSpecification(3) && SpecificationManager.spec3 != null)
				SpecificationManager.spec3.callFromMail(msg, msg.isSigned());
	}
}