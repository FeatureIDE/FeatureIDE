class Application {
	
	/*@
	 @ ensures account.getWithdraw() == 0;
	 @*/
	void nextDay() {
		original();
		account.resetWithdraw();
	}

}