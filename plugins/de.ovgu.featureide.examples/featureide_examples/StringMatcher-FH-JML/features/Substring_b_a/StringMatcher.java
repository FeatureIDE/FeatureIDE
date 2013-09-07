public  class   StringMatcher {
	
	/*@
	  @ requires \original;
	  @ ensures \original;
	  @*/
	public boolean compare(String a, String b){
		boolean result = original(a,b) &&   a.indexOf(b);
		//@ set compare = compare &&   a.indexOf(b);
		return result;
	}
}