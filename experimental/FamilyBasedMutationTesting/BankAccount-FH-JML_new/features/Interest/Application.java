class Application {
	
	/*@
	 @ ensures \original 
	 @   && (account.balance >= 0 ==> account.interest >= \old(account.interest)) 
	 @   && (account.balance <= 0 ==> account.interest <= \old(account.interest));
	 @*/
	void nextDay() {
		original();
		account.interest += account.calculateInterest();
	}

	/*@
	 @ ensures account.balance == \old(account.balance) + \old(account.interest) 
	 @   && account.interest == 0;
	 @*/
	void nextYear() {
		original();
		account.balance += account.interest;
		account.interest = 0;
	}

}