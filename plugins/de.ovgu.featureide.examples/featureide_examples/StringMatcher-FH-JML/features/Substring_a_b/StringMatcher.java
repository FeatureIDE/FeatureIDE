public  class   StringMatcher {
	
	/*@
	  @ requires \original;
	  @ ensures \original;
	  @*/
	public boolean compare(String a, String b){
		boolean result = original(a,b) &&  b.indexOf(a) != -1;
		//@ set compare = compare &&  b.indexOf(a) != -1;
		return result;
	}
	
	

	
}