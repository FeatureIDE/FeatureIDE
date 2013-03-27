package EmailSystem;

public class Email {

	protected int id;
	protected String subject;
	protected String body;
	protected Client from;
	protected String to;
	
	static int emailCounter = 1;

	public Email(int id) {
		this.id = id;
	}

	static Email createEmail(Client from, String to, String subject, String body) {
		Email msg = new Email(emailCounter++);
		msg.setEmailFrom(from);
		msg.setEmailTo(to);
		msg.setEmailSubject(subject);
		msg.setEmailBody(body);
		return msg;
	}

	/*@pure@*/ boolean   isReadable() {
		return true;
	}

	static void printMail(Email msg) {
		Util.prompt("ID:  " + msg.getId());
		Util.prompt("FROM: " + msg.getEmailFrom().getId());
		Util.prompt("TO: " + msg.getEmailTo());
		Util.prompt("SUBJECT: " + msg.getEmailSubject());
		Util.prompt("IS_READABLE " + msg.isReadable());
		Util.prompt("BODY: " + msg.getEmailBody());
	}

	Email cloneEmail(Email msg) {
		try {
			return (Email) this.clone();
		} catch (CloneNotSupportedException e) {
			throw new Error("Clone not supported");
		}
	}

	/*@pure@*/ Client getEmailFrom() {
		return from;
	}

	int getId() {
		return id;
	}

	String getEmailSubject() {
		return subject;
	}

	String getEmailTo() {
		return to;
	}

	void setEmailBody(String value) {
		body = value;
	}

	void setEmailFrom(Client value) {
		this.from = value;
	}

	void setEmailSubject(String value) {
		this.subject = value;
	}

	void setEmailTo(String value) {
		to = value;
	}

	String getEmailBody() {
		return body;
	}
}
