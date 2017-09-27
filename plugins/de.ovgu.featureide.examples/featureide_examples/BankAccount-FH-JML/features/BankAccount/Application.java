public class Application {
	/*@ invariant account != null; @*/
	Account account = new Account();

	/*@
	 @ requires true;
	 @ ensures true;
	 @ assignable \nothing;
	 @*/
	void nextDay() {
	}

	/*@
	 @ requires true;
	 @ ensures true;
	 @ assignable \nothing;
	 @*/
	void nextYear() {
	}

}