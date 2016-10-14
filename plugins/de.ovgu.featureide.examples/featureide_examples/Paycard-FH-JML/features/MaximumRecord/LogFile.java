public class LogFile {
    
    /*@ public normal_behavior
      @    ensures (\forall int i; 0 <= i && i<logArray.length;
      @             logArray[i].balance <= \result.balance);
      @    diverges true;
      @ */
    public /*@pure@*/ LogRecord getMaximumRecord(){
	LogRecord max = logArray[0];
	int i=1;
	//@ loop_invariant
	//@   0<=i && i <= logArray.length 
	//@   && max!=null &&
	//@   (\forall int j; 0 <= j && j<i; 
	//@     max.balance >= logArray[j].balance);
	//@ assignable max, i;
	while(i<logArray.length){
	    LogRecord lr = logArray[i++];
	    if (lr.getBalance() > max.getBalance()){
		max = lr;
	    }
	}
	return max;
    }

}
