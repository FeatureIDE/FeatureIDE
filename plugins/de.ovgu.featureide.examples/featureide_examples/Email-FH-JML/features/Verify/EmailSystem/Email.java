package EmailSystem;

public class Email {
	protected boolean isSignatureVerified;
	
	static void printMail(Email msg) {
		original(msg);
		Util.prompt("SIGNATURE VERIFIED " + msg.isSignatureVerified());
	}

	boolean isSignatureVerified() {
		return isSignatureVerified;
	}

	void setIsSignatureVerified(boolean value) {
		this.isSignatureVerified = value;
	}
}
