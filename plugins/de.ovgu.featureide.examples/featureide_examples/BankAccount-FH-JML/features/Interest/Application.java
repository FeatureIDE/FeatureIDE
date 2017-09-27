class Application {
	
	/*@ \consecutive_contract
	 @
	 @ ensures (account.balance >= 0 ==> account.interest >= \old(account.interest)) 
	 @   && (account.balance <= 0 ==> account.interest <= \old(account.interest));
	 @ assignable account.interest;
	 @*/
	void nextDay() {
		original();
		account.interest += account.calculateInterest();
	}

	/*@ \consecutive_contract
	 @
	 @ ensures account.balance == \old(account.balance) + \old(account.interest) 
	 @   && account.interest == 0;
	 @ assignable account.interest, account.balance;
	 @*/
	void nextYear() {
		original();
		account.balance += account.interest;
		account.interest = 0;
	}

}