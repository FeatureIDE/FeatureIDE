public class Application {
	/*@ public invariant FM.FeatureModel.bankaccount ==> (account != null); @*/

	public Account account = new Account();

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.bankaccount;
	 @ requires FM.FeatureModel.bankaccount ==> (true);
	 @*/
	 private void  nextDay__wrappee__BankAccount  () {
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.dailylimit || FM.FeatureModel.bankaccount;
	 @ ensures FM.FeatureModel.dailylimit ==> (account.withdraw == 0);
	 @*/
	 private void  nextDay__wrappee__DailyLimit  () {
		if (!FM.FeatureModel.dailylimit) {
			nextDay__wrappee__BankAccount();
			return;
		}
		nextDay__wrappee__BankAccount();
		account.withdraw = 0;
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.interest || FM.FeatureModel.dailylimit || FM.FeatureModel.bankaccount;
	 @ ensures !FM.FeatureModel.interest ==> FM.FeatureModel.dailylimit ==> (account.withdraw == 0);
	 @ ensures FM.FeatureModel.interest ==> (( FM.FeatureModel.dailylimit ==> (account.withdraw == 0) ) && (account.balance >= 0 ==> account.interest >= \old(account.interest)) && (account.balance <= 0 ==> account.interest <= \old(account.interest)));
	 @*/
	void nextDay() {
		if (!FM.FeatureModel.interest) {
			nextDay__wrappee__DailyLimit();
			return;
		}
		nextDay__wrappee__DailyLimit();
		account.interest += account.calculateInterest();
	}

	/*@  @*/
	 private void  nextYear__wrappee__BankAccount  () {
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.interest || FM.FeatureModel.bankaccount;
	 @ ensures FM.FeatureModel.interest ==> (account.balance == \old(account.balance) + \old(account.interest) && account.interest == 0);
	 @*/
	void nextYear() {
		if (!FM.FeatureModel.interest) {
			nextYear__wrappee__BankAccount();
			return;
		}
		nextYear__wrappee__BankAccount();
		account.balance += account.interest;
		account.interest = 0;
	}


}
