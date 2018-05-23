class Account {

	/*@
	 @ requires daysLeft >= 0;
	 @ ensures calculateInterest() >= 0 ==> \result >= interest;
	 @*/
	/*@ pure @*/ int estimatedInterest(int daysLeft) {
		return interest + daysLeft * calculateInterest();
	}

}