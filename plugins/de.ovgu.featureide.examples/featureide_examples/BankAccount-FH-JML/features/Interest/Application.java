class Application {
	
	/*@
	 @ ensures \original 
	 @   && (account.getBalance() >= 0 ==> account.getInterest() >= \old(account.getInterest())) 
	 @   && (account.getBalance() <= 0 ==> account.getInterest() <= \old(account.getInterest()));
	 @*/
	void nextDay() {
		original();
		account.increaseInterrest();
	}

	/*@ 
	 @ ensures account.getBalance() == \old(account.getBalance()) + \old(account.getInterest()) 
	 @   && account.getInterest() == 0;
	 @*/
	void nextYear() {
		original();
		account.applyInterrest();
	}

}