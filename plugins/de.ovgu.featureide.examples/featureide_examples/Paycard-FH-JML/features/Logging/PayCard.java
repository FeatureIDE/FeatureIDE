public class PayCard {
    
    /*@ spec_public @*/ protected LogFile log;
    
    // contract remains identical
    public void chargeAndRecord(int amount) {
	if (charge(amount)) {
	    try {
		log.addRecord(balance);
	    } catch (CardException e){
		throw new IllegalArgumentException();
	    }
	}
    }
    
}
