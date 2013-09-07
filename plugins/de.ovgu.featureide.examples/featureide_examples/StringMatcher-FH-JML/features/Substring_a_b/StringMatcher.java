public  class   StringMatcher {
	
	/*@
	  @ requires \original;
	  @ ensures \original;
	  @*/
	public boolean compare(String a, String b){
		boolean result = original(a,b) &&  b.indexOf(a);
		//@ set compare = compare &&  b.indexOf(a);
		return result;
	}
	
	

	
}