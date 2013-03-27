package EmailSystem;

public class Email {
	protected boolean isEncrypted;
	protected int encryptionKey;
	
	/*@pure@*/ boolean  isReadable() {
		if (!isEncrypted())
			return original();
		else
			return false;
	}
	
	static void printMail(Email msg) {
		original(msg);
		Util.prompt("ENCRYPTED " + msg.isEncrypted());
		// Util.prompt("ENCRYPTION KEY  "+ msg.getEmailEncryptionKey());
	}
	
	/*@pure@*/ boolean  isEncrypted() {
		return isEncrypted;
	}


	void setEmailIsEncrypted(boolean value) {
		isEncrypted = value;
	}

	void setEmailEncryptionKey(int value) {
		this.encryptionKey = value;
	}

	/*@pure@*/ int getEmailEncryptionKey() {
		return encryptionKey;
	}
}
