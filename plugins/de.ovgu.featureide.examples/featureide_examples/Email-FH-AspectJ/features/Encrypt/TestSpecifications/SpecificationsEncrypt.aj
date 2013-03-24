package TestSpecifications;

import EmailSystem.Client;
import EmailSystem.Email;

privileged public aspect SpecificationsEncrypt {
	 before(Client client, Email msg) : 
		 call(static void EmailSystem.Client.mail(Client, Email)) 
		 && args(client, msg) {
		 // encrypt
			if ((SpecificationManager.checkSpecification(1) && SpecificationManager.spec1_8!= null)
					|| (SpecificationManager.checkSpecification(8) && SpecificationManager.spec1_8!= null))
				SpecificationManager.spec1_8.callFromMail(msg, msg.isEncrypted());
			if (SpecificationManager.checkSpecification(6) && SpecificationManager.spec6 != null)
				SpecificationManager.spec6.callFromMail(msg, msg.isEncrypted());
			if (SpecificationManager.checkSpecification(9) && SpecificationManager.spec9 != null)
				SpecificationManager.spec9.callFromMail(msg, msg.isEncrypted());
	 }
	 before(Client client, Email msg) : 
		 call(static void  EmailSystem.Client.incoming(Client, Email)) 
		 && args(client, msg) {
		 // encrypt
		if (SpecificationManager.checkSpecification(9) && SpecificationManager.spec9 != null) {
			SpecificationManager.spec9.callFromIncoming(msg, msg.isEncrypted());
		}
		// this was in Incoming_role_decrypt
		if (SpecificationManager.checkSpecification(6) && SpecificationManager.spec6 != null) {
			SpecificationManager.spec6.callFromIncoming__role__Decrypt(msg, msg.getEmailEncryptionKey(), client.getPrivateKey());
		}
	 }
}