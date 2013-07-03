public  class   StringMatcher {
	
	/*@
	  @ requires \original;
	  @ ensures \original;
	  @*/
	public boolean compare(String a, String b){
		boolean result = original(a,b) &&  contains(b,a);
		//@ set compare = compare &&  contains(b,a);
		return result;
	}
	
	

	
}