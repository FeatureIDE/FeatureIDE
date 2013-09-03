public  class   StringMatcher {
	
	
	/*@
	  @ requires \original;
	  @ ensures \original;
	  @*/
	public boolean compare(String a, String b){
		boolean result = original(a,b) &&   a.startsWith(b);
		//@ set compare = compare && a.startsWith(b);
		return result;
	}
	

	
}