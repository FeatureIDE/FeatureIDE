class Application {
	
	/*@
	 @ ensures account.getWithdraw().getValue() == 0;
	 @*/
	void nextDay() {
		original();
		account.resetWithdraw();
	}

}