class Application {
	
	/*@ \consecutive_contract
	 @
	 @ ensures account.withdraw == 0;
	 @ assignable account.withdraw;
	 @*/
	void nextDay() {
		original();
		account.withdraw = 0;
	}

}