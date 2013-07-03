public  class   StringMatcher {
	
	/*@
	  @ requires \original;
	  @ ensures \original;
	  @*/
	public boolean compare(String a, String b){
		boolean result = original(a,b) &&  contains(a,b);
		//@ set compare = compare &&  contains(a,b);
		return result;
	}
}