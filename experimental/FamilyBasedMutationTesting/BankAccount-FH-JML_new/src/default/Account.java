public  class Account {
	public final int OVERDRAFT_LIMIT  = FM.FeatureModel.overdraft ?  -5000 :  0;

	/*@ public invariant FM.FeatureModel.bankaccount ==> (this.balance >= OVERDRAFT_LIMIT); @*/

	public int balance = 0;

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.bankaccount;
	 @ ensures FM.FeatureModel.bankaccount ==> (balance == 0);
	 @*/
	Account() {
		if (FM.FeatureModel.bankaccount) {
				}
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.bankaccount;
	 @ requires FM.FeatureModel.bankaccount ==> (x != 0);
	 @ ensures FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) 
	 @ && (\result ==> balance == \old(balance) + x));
	 @*/
	 private boolean  update__wrappee__BankAccount  (int x) {
		int newBalance = balance + x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = balance + x;
		return true;
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.dailylimit || FM.FeatureModel.bankaccount;
	 @ requires !FM.FeatureModel.dailylimit ==> FM.FeatureModel.bankaccount ==> (x != 0);
	 @ requires FM.FeatureModel.dailylimit ==> (( FM.FeatureModel.bankaccount ==> (x != 0) ));
	 @ ensures !FM.FeatureModel.dailylimit ==> FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) && (\result ==> balance == \old(balance) + x));
	 @ ensures FM.FeatureModel.dailylimit ==> (( FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) && (\result ==> balance == \old(balance) + x)) ));
	 @ ensures FM.FeatureModel.dailylimit ==> ((!\result ==> withdraw == \old(withdraw)) && (\result ==> withdraw <= \old(withdraw)));
	 @*/
	 private boolean  update__wrappee__DailyLimit  (int x) {
		if (!FM.FeatureModel.dailylimit)
			return update__wrappee__BankAccount(x);
		int newWithdraw = withdraw;
		if (x < 0)  {
			newWithdraw += x;
			if (newWithdraw < DAILY_LIMIT) 
				return false;
		}
		if (!update__wrappee__BankAccount(x))
			return false;
		withdraw = newWithdraw;
		return true;
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.logging || FM.FeatureModel.dailylimit || FM.FeatureModel.bankaccount;
	 @ ensures !FM.FeatureModel.logging ==> FM.FeatureModel.dailylimit ==> ((!\result ==> withdraw == \old(withdraw)) && (\result ==> withdraw <= \old(withdraw)));
	 @ ensures !FM.FeatureModel.logging ==> FM.FeatureModel.dailylimit ==> (( FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) && (\result ==> balance == \old(balance) + x)) ));
	 @ ensures !FM.FeatureModel.logging ==> !FM.FeatureModel.dailylimit ==> FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) && (\result ==> balance == \old(balance) + x));
	 @ ensures FM.FeatureModel.logging ==> (( !FM.FeatureModel.dailylimit ==> FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) && (\result ==> balance == \old(balance) + x)) ) && ( FM.FeatureModel.dailylimit ==> (( FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) && (\result ==> balance == \old(balance) + x)) )) ) && ( FM.FeatureModel.dailylimit ==> ((!\result ==> withdraw == \old(withdraw)) && (\result ==> withdraw <= \old(withdraw))) ));
	 @ ensures FM.FeatureModel.logging ==> (\result ==> this.updates[this.updateCounter] == x);
	 @ ensures FM.FeatureModel.logging ==> (\result ==> this.updateCounter == ( \old(this.updateCounter) + 1 ) % 10);
	 @ ensures FM.FeatureModel.logging ==> (!\result ==> this.updateCounter == \old(this.updateCounter));
	 @*/
	boolean update(int x){
		if (!FM.FeatureModel.logging)
			return update__wrappee__DailyLimit(x);
		if (update__wrappee__DailyLimit(x)){
			updateCounter = (updateCounter + 1) % 10;
			updates[updateCounter] = x;
			return true;
		}
		return false;
		
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.bankaccount;
	 @ ensures FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) 
	 @ && (\result ==> balance == \old(balance) - x));
	 @*/
	 private boolean  undoUpdate__wrappee__BankAccount  (int x) {
		int newBalance = balance - x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.dailylimit || FM.FeatureModel.bankaccount;
	 @ ensures !FM.FeatureModel.dailylimit ==> FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) && (\result ==> balance == \old(balance) - x));
	 @ ensures FM.FeatureModel.dailylimit ==> (( FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) && (\result ==> balance == \old(balance) - x)) ));
	 @ ensures FM.FeatureModel.dailylimit ==> ((!\result ==> withdraw == \old(withdraw)) && (\result ==> withdraw >= \old(withdraw)));
	 @*/
	 private boolean  undoUpdate__wrappee__DailyLimit  (int x) {
		if (!FM.FeatureModel.dailylimit)
			return undoUpdate__wrappee__BankAccount(x);
		int newWithdraw = withdraw;
		if (x < 0)  {
			newWithdraw -= x;
			if (newWithdraw < DAILY_LIMIT) 
				return false;
		}
		if (!undoUpdate__wrappee__BankAccount(x))
			return false;
		withdraw = newWithdraw;
		return true;
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.logging || FM.FeatureModel.dailylimit || FM.FeatureModel.bankaccount;
	 @ ensures !FM.FeatureModel.logging ==> FM.FeatureModel.dailylimit ==> ((!\result ==> withdraw == \old(withdraw)) && (\result ==> withdraw >= \old(withdraw)));
	 @ ensures !FM.FeatureModel.logging ==> FM.FeatureModel.dailylimit ==> (( FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) && (\result ==> balance == \old(balance) - x)) ));
	 @ ensures !FM.FeatureModel.logging ==> !FM.FeatureModel.dailylimit ==> FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) && (\result ==> balance == \old(balance) - x));
	 @ ensures FM.FeatureModel.logging ==> (( !FM.FeatureModel.dailylimit ==> FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) && (\result ==> balance == \old(balance) - x)) ) && ( FM.FeatureModel.dailylimit ==> (( FM.FeatureModel.bankaccount ==> ((!\result ==> balance == \old(balance)) && (\result ==> balance == \old(balance) - x)) )) ) && ( FM.FeatureModel.dailylimit ==> ((!\result ==> withdraw == \old(withdraw)) && (\result ==> withdraw >= \old(withdraw))) ));
	 @ ensures FM.FeatureModel.logging ==> (\result ==> this.undoUpdates[this.undoUpdateCounter] == x);
	 @ ensures FM.FeatureModel.logging ==> (\result ==> this.undoUpdateCounter == ( \old(this.undoUpdateCounter) + 1 ) % 10);
	 @ ensures FM.FeatureModel.logging ==> (!\result ==> this.undoUpdateCounter == \old(this.undoUpdateCounter));
	 @*/
	boolean undoUpdate(int x){
		if (!FM.FeatureModel.logging)
			return undoUpdate__wrappee__DailyLimit(x);
		if (undoUpdate__wrappee__DailyLimit(x)){
			undoUpdateCounter = (undoUpdateCounter + 1) % 10;
			undoUpdates[undoUpdateCounter] = x;
			return true;
		}
		return false;
		
	}

	public final static int DAILY_LIMIT = -1000;

	/*@ public invariant FM.FeatureModel.dailylimit ==> (withdraw >= DAILY_LIMIT); @*/

	public int withdraw = 0;

	final static int INTEREST_RATE = 2;

	int interest = 0;

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.interest;
	 @ ensures FM.FeatureModel.interest ==> ((balance >= 0 ==> \result >= 0) 
	 @ && (balance <= 0 ==> \result <= 0));
	 @*/
	 /*@pure@*/  int calculateInterest() {
		return balance * INTEREST_RATE / 36500;
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.interestestimation;
	 @ requires FM.FeatureModel.interestestimation ==> (daysLeft >= 0);
	 @ ensures FM.FeatureModel.interestestimation ==> (calculateInterest() >= 0 ==> \result >= interest);
	 @*/
	 /*@pure@*/  int estimatedInterest(int daysLeft) {
		return interest + daysLeft * calculateInterest();
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.creditworthiness;
	 @ requires FM.FeatureModel.creditworthiness ==> (amount >= 0);
	 @ ensures FM.FeatureModel.creditworthiness ==> (balance >= amount <==> \result);
	 @*/
	boolean credit(int amount) {
		return balance >= amount;
	}

	public boolean lock = false;

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.lock;
	 @ ensures FM.FeatureModel.lock ==> (this.lock);
	 @*/
	void lock() {
		lock = true;
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.lock;
	 @ ensures FM.FeatureModel.lock ==> (!this.lock);
	 @*/
	void unLock() {
		lock = false;
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.lock;
	 @ ensures FM.FeatureModel.lock ==> (\result == this. lock);
	 @*/
	boolean isLocked() {
		return lock;
	}

	public int[] updates = new int[10];

	public int updateCounter = 0;

	public int[] undoUpdates = new int[10];

	public int undoUpdateCounter = 0;


}
